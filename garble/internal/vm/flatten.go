package vm

import (
	"fmt"
	mathrand "math/rand"
)

// FlattenOptions configures control-flow flattening of virtual functions.
//
// Flattening replaces the direct branches of a virtual function with an
// indirect dispatch: every basic block ends by pushing a state word and
// executing OpDispatch, which transfers control through a per-function table.
// The state assigned to a block and the physical order of the blocks are two
// independent permutations, and unused table slots are filled with decoy
// targets, so neither the bytecode layout nor the table reveals the original
// control-flow graph. The tables themselves are stored key-encoded in the
// emitted program.
//
// Flattening is semantics-preserving: it only changes how control flows between
// blocks, never what the blocks compute.
type FlattenOptions struct {
	// Seed drives the block and state permutations. Two flattens of the same
	// program with the same seed produce identical output, which keeps garble's
	// builds reproducible. A zero seed falls back to the program key.
	Seed uint64
	// DecoyEdges inserts, before each dispatch, a predicate that is always
	// false-looking but in fact always holds, followed by a block that is never
	// executed. An analyst who follows the handlers sees a plausible extra edge
	// at every branch. The predicated sequence costs extra instructions on
	// every branch, so it is off by default.
	DecoyEdges bool
	// TablePadding is the number of unused entries to add to each dispatch
	// table. Each one points at a real block, so an analyst cannot tell which
	// states the code actually reaches without solving the state permutations.
	TablePadding int
}

// DefaultFlattenOptions returns the recommended flattening settings for a seed.
func DefaultFlattenOptions(seed uint64) FlattenOptions {
	// Hardened defaults: larger decoy table and opaque decoy edges enabled.
	return FlattenOptions{Seed: seed, TablePadding: 16, DecoyEdges: true}
}

func (o FlattenOptions) normalized(key uint64) FlattenOptions {
	if o.Seed == 0 {
		o.Seed = key
	}
	if o.TablePadding < 0 {
		o.TablePadding = 0
	}
	return o
}

// Flatten rewrites every virtual function of the program into control-flow
// flattened form. The program key is used to decode and re-encode the bytecode,
// so Flatten must be called on the Program the code belongs to.
//
// Every rewritten function is re-verified before it is installed, so a bug in
// the transformation is reported as a build error rather than as miscompiled
// bytecode. If a function fails to flatten, the program is left untouched.
func (p *Program) Flatten(opts FlattenOptions) error {
	opts = opts.normalized(p.Key)

	// Snapshot the program so that a failure at any point leaves it exactly as
	// it was: flattening is all-or-nothing, not per-function.
	type snapshot struct {
		code     []byte
		dispatch []int32
		maxStack int
	}
	saved := make([]snapshot, len(p.Funcs))
	for i, f := range p.Funcs {
		if f == nil {
			return fmt.Errorf("vm: flatten: function %d is nil", i)
		}
		saved[i] = snapshot{f.Code, f.Dispatch, f.MaxStack}
	}
	for _, f := range p.Funcs {
		if err := p.flattenFunc(f, opts); err != nil {
			for j, g := range p.Funcs {
				g.Code, g.Dispatch, g.MaxStack = saved[j].code, saved[j].dispatch, saved[j].maxStack
			}
			return err
		}
	}
	p.ComputeIntegrity()
	return nil
}

// flatKind classifies how a basic block transfers control.
type flatKind int

const (
	// flatFallsThrough reaches the next block in the original layout.
	flatFallsThrough flatKind = iota
	// flatJump ends in an unconditional branch.
	flatJump
	// flatCond ends in a conditional branch.
	flatCond
	// flatTerminal ends in OpReturn or OpHalt.
	flatTerminal
)

// flatBlock is one basic block of the original bytecode, described by the range
// of instructions it covers.
type flatBlock struct {
	start, end int // instruction indices; end is exclusive
	kind       flatKind
	// target is the instruction index the block branches to, for flatJump and
	// flatCond.
	target int
	// next is the index of the block reached when the block falls through, or
	// -1 when there is none.
	next int
}

// flatBlocks splits a decoded body into basic blocks. A block starts at a
// control-flow leader and ends immediately before the next leader, so a block
// need not end in a branch: it may simply fall through to the next block.
func flatBlocks(instrs []Instruction) ([]flatBlock, error) {
	if len(instrs) == 0 {
		return nil, nil
	}
	// instrIndex converts a branch operand into an instruction index, rejecting
	// anything that is not an instruction boundary inside the body.
	instrIndex := func(arg int64) (int, error) {
		if arg < 0 || arg%InstrSize != 0 || int(arg) >= len(instrs)*InstrSize {
			return 0, fmt.Errorf("branch target %d is not a valid instruction boundary", arg)
		}
		return int(arg) / InstrSize, nil
	}

	leader := map[int]bool{0: true}
	for i, instr := range instrs {
		switch instr.Op {
		case OpDispatch:
			return nil, fmt.Errorf("function is already flattened (OpDispatch at %04d)", i*InstrSize)
		case OpJump:
			idx, err := instrIndex(instr.Arg)
			if err != nil {
				return nil, err
			}
			leader[idx] = true
		case OpJumpIfZero, OpJumpIfNotZero:
			idx, err := instrIndex(instr.Arg)
			if err != nil {
				return nil, err
			}
			leader[idx] = true
			// The instruction after a conditional is only ever reached by
			// falling through, so it begins a block of its own.
			if i+1 < len(instrs) {
				leader[i+1] = true
			}
		}
	}

	starts := make([]int, 0, len(leader))
	for i := range instrs {
		if leader[i] {
			starts = append(starts, i)
		}
	}

	blocks := make([]flatBlock, len(starts))
	for b, start := range starts {
		end := len(instrs)
		next := -1
		if b+1 < len(starts) {
			end = starts[b+1]
			next = b + 1
		}
		// A block may only transfer control with its last instruction. Code
		// after a branch is unreachable, which the verifier rejects, but checking
		// here keeps the rewrite safe even on a hand-built program.
		for i := start; i < end-1; i++ {
			if flatIsControl(instrs[i].Op) {
				return nil, fmt.Errorf("control instruction %s at %04d is followed by more instructions", instrs[i].Op, i*InstrSize)
			}
		}

		blk := flatBlock{start: start, end: end, next: next}
		switch last := instrs[end-1]; last.Op {
		case OpJump:
			idx, err := instrIndex(last.Arg)
			if err != nil {
				return nil, err
			}
			blk.kind, blk.target = flatJump, idx
		case OpJumpIfZero, OpJumpIfNotZero:
			idx, err := instrIndex(last.Arg)
			if err != nil {
				return nil, err
			}
			blk.kind, blk.target = flatCond, idx
			if blk.next < 0 {
				return nil, fmt.Errorf("conditional block at %04d has no fallthrough block", start*InstrSize)
			}
		case OpReturn, OpHalt:
			blk.kind = flatTerminal
		default:
			if blk.next < 0 {
				return nil, fmt.Errorf("block at %04d falls off the end of the function", start*InstrSize)
			}
			blk.kind = flatFallsThrough
		}
		blocks[b] = blk
	}
	return blocks, nil
}

// flatIsControl reports whether op transfers control, and therefore must be the
// last instruction of a basic block.
func flatIsControl(op Opcode) bool {
	switch op {
	case OpJump, OpJumpIfZero, OpJumpIfNotZero, OpReturn, OpDispatch, OpHalt:
		return true
	}
	return false
}

// decoyPredicateLen is the number of instructions emitted for a decoy predicate.
const decoyPredicateLen = 8

// emitDecoyPredicate emits a sequence that computes a predicate which is always
// false, then branches to deadOffset when it is true. The branch is therefore
// never taken, but it is a real edge as far as any static reader is concerned.
//
// For every integer x, x and x+1 have opposite parity, so x*(x+1) is even and
// its low bit is zero even under wrapping arithmetic. The predicate looks
// data-dependent because it reads a live frame slot.
func emitDecoyPredicate(b *Builder, slot int, deadOffset int64) {
	b.Emit(OpLoadLocal, int64(slot))
	b.Emit(OpLoadLocal, int64(slot))
	b.Emit(OpConst, 1)
	b.Emit(OpAddI, 0)
	b.Emit(OpMulI, 0)
	b.Emit(OpConst, 1)
	b.Emit(OpAnd, 0)
	b.Emit(OpJumpIfNotZero, deadOffset)
}

// pickDecoySlot chooses an integer-typed frame slot for the decoy predicate, if
// the function has one. The predicate must read a word the machine treats as an
// integer, so float slots are never used.
func pickDecoySlot(f *Function) (int, bool) {
	for slot, ty := range f.LocalTypes {
		if ty == TypeInt {
			return slot, true
		}
	}
	return 0, false
}

// flattenFunc rewrites one function in place. It returns an error without
// modifying f if the rewrite does not verify.
func (p *Program) flattenFunc(f *Function, opts FlattenOptions) error {
	if len(f.Code) == 0 {
		return nil
	}
	if len(f.Code)%InstrSize != 0 {
		return fmt.Errorf("vm: flatten %s: code length %d is not a multiple of %d", f.Name, len(f.Code), InstrSize)
	}
	instrs := make([]Instruction, f.NumInstrs())
	for i := range instrs {
		instrs[i] = DecodeHard(f.Code, i*InstrSize, p.Key, p.Hardening)
	}

	blocks, err := flatBlocks(instrs)
	if err != nil {
		return fmt.Errorf("vm: flatten %s: %w", f.Name, err)
	}
	if len(blocks) == 0 {
		return nil
	}
	numBlocks := len(blocks)

	blockOf := make(map[int]int, numBlocks)
	for b, blk := range blocks {
		blockOf[blk.start] = b
	}

	// Decoys need an integer slot to read; without one the function simply gets
	// the plain flattened form.
	decoySlot, hasDecoySlot := pickDecoySlot(f)
	useDecoys := opts.DecoyEdges && hasDecoySlot

	// Two independent permutations: one orders the blocks physically, the other
	// numbers the states. Both are derived from the seed, so the result is
	// reproducible.
	rng := mathrand.New(mathrand.NewSource(int64(opts.Seed)))
	layout := rng.Perm(numBlocks)
	tableLen := numBlocks + opts.TablePadding
	states := rng.Perm(tableLen)

	// unitSize is the number of instructions each block's rewritten unit takes.
	unitSize := make([]int, numBlocks)
	for b, blk := range blocks {
		body := blk.end - blk.start
		switch blk.kind {
		case flatTerminal:
			unitSize[b] = body
		case flatJump:
			// The branch is replaced by Const/Dispatch.
			unitSize[b] = body - 1 + 2
		case flatFallsThrough:
			unitSize[b] = body + 2
		case flatCond:
			// The conditional is re-emitted with a rewritten target, followed
			// by the next-state dispatch and the taken stub.
			unitSize[b] = body - 1 + 1 + 2 + 2
		}
		if useDecoys && blk.kind != flatTerminal {
			unitSize[b] += decoyPredicateLen + 2
		}
	}

	// Lay the blocks out and record where each one starts.
	unitStart := make([]int64, numBlocks)
	offset := int64(2 * InstrSize) // the entry prologue
	for _, b := range layout {
		unitStart[b] = offset
		offset += int64(unitSize[b]) * InstrSize
	}

	b := NewBuilder()
	b.Emit(OpConst, int64(states[0])) // the entry block is always block 0
	b.Emit(OpDispatch, 0)

	for _, k := range layout {
		blk := blocks[k]
		bodyEnd := blk.end
		if blk.kind == flatJump || blk.kind == flatCond {
			bodyEnd-- // the branch is re-emitted below
		}
		for _, instr := range instrs[blk.start:bodyEnd] {
			b.Emit(instr.Op, instr.Arg)
		}

		switch blk.kind {
		case flatTerminal:
			// Nothing to add: the block already ends the frame.

		case flatJump:
			succ := blockOf[blk.target]
			decoy := (succ + 1) % numBlocks
			dead := unitStart[k] + int64(unitSize[k]-2)*InstrSize
			if useDecoys {
				emitDecoyPredicate(b, decoySlot, dead)
			}
			b.Emit(OpConst, int64(states[succ]))
			b.Emit(OpDispatch, 0)
			if useDecoys {
				b.Emit(OpConst, int64(states[decoy]))
				b.Emit(OpDispatch, 0)
			}

		case flatFallsThrough:
			succ := blk.next
			decoy := (succ + 1) % numBlocks
			dead := unitStart[k] + int64(unitSize[k]-2)*InstrSize
			if useDecoys {
				emitDecoyPredicate(b, decoySlot, dead)
			}
			b.Emit(OpConst, int64(states[succ]))
			b.Emit(OpDispatch, 0)
			if useDecoys {
				b.Emit(OpConst, int64(states[decoy]))
				b.Emit(OpDispatch, 0)
			}

		case flatCond:
			taken := blockOf[blk.target]
			// The stub sits in the last two instructions of the unit; when
			// decoys are on, the dead stub sits immediately before it.
			stub := unitStart[k] + int64(unitSize[k]-2)*InstrSize
			b.Emit(instrs[blk.end-1].Op, stub)
			if useDecoys {
				dead := stub - 2*InstrSize
				emitDecoyPredicate(b, decoySlot, dead)
			}
			b.Emit(OpConst, int64(states[blk.next]))
			b.Emit(OpDispatch, 0)
			if useDecoys {
				b.Emit(OpConst, int64(states[(taken+1)%numBlocks]))
				b.Emit(OpDispatch, 0)
			}
			b.Emit(OpConst, int64(states[taken]))
			b.Emit(OpDispatch, 0)
		}
	}

	// The block offsets computed above must match the emission exactly; a
	// mismatch would silently mis-encode every branch target. The verification
	// below is the second line of defence, but this catches the bookkeeping bug
	// at its source.
	if emitted := int64(b.Len()); emitted != offset {
		return fmt.Errorf("vm: flatten %s: internal error: laid out %d bytes but emitted %d", f.Name, offset, emitted)
	}

	// Build the dispatch table. Unused slots point at real blocks so that they
	// look exactly like live states.
	table := make([]int32, tableLen)
	assigned := make([]bool, tableLen)
	for b := range blocks {
		table[states[b]] = int32(unitStart[b])
		assigned[states[b]] = true
	}
	for slot := range table {
		if !assigned[slot] {
			table[slot] = int32(unitStart[rng.Intn(numBlocks)])
		}
	}

	// Install the rewrite and re-verify it. Flatten restores the whole program
	// if this fails, so a caller never sees a half-rewritten program.
	f.Code, f.Dispatch = b.EncodeHard(p.Key, p.Hardening), table
	if err := p.verifyFunc(f); err != nil {
		return fmt.Errorf("vm: flatten %s: rewritten function does not verify: %w", f.Name, err)
	}
	return nil
}
