package vm

import (
	"fmt"
	"strings"
)

// MaxStackLimit bounds the operand stack depth a function may require. It keeps
// verification terminating and rejects pathological or malformed input early.
const MaxStackLimit = 4096

// MaxLocalsLimit bounds the number of frame slots a function may declare.
const MaxLocalsLimit = 4096

// VerifyError describes a rejected program. It is returned rather than panicking
// so that the compiler can fall back to leaving the offending function native.
type VerifyError struct {
	// Func is the name of the function that failed verification.
	Func string
	// PC is the byte offset of the offending instruction, or -1 when the error
	// is not tied to a single instruction.
	PC  int
	Msg string
}

func (e *VerifyError) Error() string {
	if e.PC < 0 {
		return fmt.Sprintf("vm: verify %s: %s", e.Func, e.Msg)
	}
	return fmt.Sprintf("vm: verify %s at %04d: %s", e.Func, e.PC, e.Msg)
}

func verifyErrf(f *Function, pc int, format string, args ...any) error {
	return &VerifyError{Func: f.Name, PC: pc, Msg: fmt.Sprintf(format, args...)}
}

// stackState is the abstract state at a program point: the operand stack, from
// bottom to top.
type stackState []ValType

func (s stackState) clone() stackState {
	return append(stackState(nil), s...)
}

func (s stackState) equal(other stackState) bool {
	if len(s) != len(other) {
		return false
	}
	for i := range s {
		if s[i] != other[i] {
			return false
		}
	}
	return true
}

// join merges two abstract stacks. It returns the merged state and whether the
// merge is well formed. States with different heights cannot be merged: a
// program where a control-flow join sees two different stack depths has no
// single meaning and is rejected.
func (s stackState) join(other stackState) (stackState, bool) {
	if len(s) != len(other) {
		return nil, false
	}
	merged := make(stackState, len(s))
	for i := range s {
		merged[i] = s[i].join(other[i])
	}
	return merged, true
}

// Verify checks the whole program and computes each function's MaxStack.
func (p *Program) Verify() error {
	for _, f := range p.Funcs {
		if f == nil {
			return fmt.Errorf("vm: verify: nil function in program")
		}
		if err := p.verifyFunc(f); err != nil {
			return err
		}
	}
	return nil
}

// VerifyFunc verifies a single function within the program context, which is
// needed to resolve OpCallV and OpCallN targets.
func (p *Program) VerifyFunc(f *Function) error { return p.verifyFunc(f) }

func (p *Program) verifyFunc(f *Function) error {
	if len(f.Code) == 0 {
		return verifyErrf(f, -1, "empty code")
	}
	if len(f.Code)%InstrSize != 0 {
		return verifyErrf(f, -1, "code length %d is not a multiple of %d", len(f.Code), InstrSize)
	}
	if f.NumLocals < 0 || f.NumLocals > MaxLocalsLimit {
		return verifyErrf(f, -1, "num locals %d out of range", f.NumLocals)
	}
	if len(f.LocalTypes) != f.NumLocals {
		return verifyErrf(f, -1, "local types length %d does not match num locals %d", len(f.LocalTypes), f.NumLocals)
	}
	if len(f.Params) > f.NumLocals {
		return verifyErrf(f, -1, "more parameters (%d) than locals (%d)", len(f.Params), f.NumLocals)
	}
	if len(f.Results) > MaxStackLimit {
		return verifyErrf(f, -1, "too many results (%d)", len(f.Results))
	}
	if f.Params == nil {
		f.Params = []ValType{}
	}
	if f.Results == nil {
		f.Results = []ValType{}
	}

	instrs := make([]Instruction, f.NumInstrs())
	for i := range instrs {
		instrs[i] = DecodeHard(f.Code, i*InstrSize, p.Key, p.Hardening)
	}

	// states[pc] is the abstract stack on entry to the instruction at pc.
	states := make(map[int]stackState)
	states[0] = stackState{}

	type workItem struct{ pc int }
	work := []workItem{{0}}

	// A local slot may be stored from several places; track the joined type per
	// slot so that a load after divergent stores is still type-consistent.
	localTypes := append([]ValType(nil), f.LocalTypes...)
	for i := range localTypes {
		if localTypes[i] == 0 && i >= len(f.Params) {
			localTypes[i] = TypeAny
		}
	}

	maxStack := 0

	// bound the number of reprocessed states to guarantee termination even for
	// adversarial input that keeps widening types.
	steps := 0
	maxSteps := f.NumInstrs()*f.NumInstrs() + 64

	// poisonOffEnd marks a control path that would run past the last
	// instruction. It is distinguished from the height-mismatch poison so the
	// diagnostic names the real problem.
	const (
		poisonMerge  ValType = 0xfe
		poisonOffEnd ValType = 0xff
	)

	successor := func(pc int, st stackState) {
		if len(st) > MaxStackLimit {
			return // reported below
		}
		if pc == len(f.Code) {
			// Reuse the poison encoding to carry the reason.
			if _, ok := states[pc]; !ok {
				states[pc] = stackState{poisonOffEnd}
				work = append(work, workItem{pc})
			}
			return
		}
		if old, ok := states[pc]; ok {
			merged, ok := old.join(st)
			if !ok {
				// Heights differ at a join. Record a poison marker so the error
				// is reported with a useful location.
				states[pc] = stackState{poisonMerge}
				work = append(work, workItem{pc})
				return
			}
			if merged.equal(old) {
				return
			}
			states[pc] = merged
		} else {
			states[pc] = st.clone()
		}
		work = append(work, workItem{pc})
	}

	for len(work) > 0 {
		steps++
		if steps > maxSteps {
			return verifyErrf(f, -1, "verification did not converge")
		}
		item := work[0]
		work = work[1:]
		pc := item.pc

		st := states[pc]
		if len(st) == 1 && st[0] == poisonOffEnd {
			return verifyErrf(f, pc, "control falls off the end of the function")
		}
		if len(st) == 1 && st[0] == poisonMerge {
			return verifyErrf(f, pc, "incompatible stack depths at control-flow merge")
		}
		if pc%InstrSize != 0 || pc < 0 || pc >= len(f.Code) {
			return verifyErrf(f, pc, "invalid instruction offset")
		}
		if len(st) > maxStack {
			maxStack = len(st)
		}

		instr := instrs[pc/InstrSize]
		op := instr.Op
		fallthroughPC := pc + InstrSize

		checkDepth := func(n int) error {
			if len(st) < n {
				return verifyErrf(f, pc, "%s requires %d operand(s), stack has %d", op, n, len(st))
			}
			return nil
		}
		// checkTypes compares the top len(types) words against types, which is
		// given in push order: types[0] describes the deepest word of the group
		// and types[len-1] the top of the stack. Call arguments, return values
		// and the fixed-table operand groups all follow that convention.
		checkTypes := func(types []ValType) error {
			n := len(types)
			for i, want := range types {
				got := st[len(st)-n+i]
				if want == TypeAny || got == TypeAny || want == got {
					continue
				}
				return verifyErrf(f, pc, "%s operand %d (of %d) has type %s, want %s", op, i, n, got, want)
			}
			return nil
		}
		popN := func(n int) stackState { return st[:len(st)-n].clone() }
		// applyEffect handles every instruction described by the fixed table.
		applyEffect := func(eff stackEffect) error {
			if err := checkDepth(eff.pop); err != nil {
				return err
			}
			if err := checkTypes(eff.popTy); err != nil {
				return err
			}
			next := popN(eff.pop)
			for i := 0; i < eff.push; i++ {
				next = append(next, eff.pushTy)
			}
			successor(fallthroughPC, next)
			return nil
		}
		branch := func(target int, next stackState) error {
			if target%InstrSize != 0 || target < 0 || target >= len(f.Code) {
				return verifyErrf(f, pc, "branch target %d is not a valid instruction boundary", target)
			}
			successor(target, next)
			return nil
		}

		var err error
		switch op {
		case OpDup:
			if err = checkDepth(1); err != nil {
				break
			}
			next := append(st.clone(), st[len(st)-1])
			successor(fallthroughPC, next)
		case OpSwap:
			if err = checkDepth(2); err != nil {
				break
			}
			next := st.clone()
			next[len(next)-1], next[len(next)-2] = next[len(next)-2], next[len(next)-1]
			successor(fallthroughPC, next)
		case OpLoadLocal:
			if instr.Arg < 0 || int(instr.Arg) >= f.NumLocals {
				err = verifyErrf(f, pc, "load of local %d out of range [0,%d)", instr.Arg, f.NumLocals)
				break
			}
			successor(fallthroughPC, append(st.clone(), localTypes[instr.Arg]))
		case OpStoreLocal:
			if instr.Arg < 0 || int(instr.Arg) >= f.NumLocals {
				err = verifyErrf(f, pc, "store to local %d out of range [0,%d)", instr.Arg, f.NumLocals)
				break
			}
			if err = checkDepth(1); err != nil {
				break
			}
			val := st[len(st)-1]
			if slot := localTypes[instr.Arg]; slot != TypeAny && val != TypeAny && slot != val {
				err = verifyErrf(f, pc, "store of %s into %s local %d", val, slot, instr.Arg)
				break
			}
			successor(fallthroughPC, popN(1))
		case OpConvert:
			if err = checkDepth(1); err != nil {
				break
			}
			fromKind, fromBits, toKind, toBits := UnpackConvertOperand(instr.Arg)
			fromTy, ok := convertKindType(fromKind, fromBits)
			if !ok {
				err = verifyErrf(f, pc, "invalid conversion source kind=%d bits=%d", fromKind, fromBits)
				break
			}
			toTy, ok := convertKindType(toKind, toBits)
			if !ok {
				err = verifyErrf(f, pc, "invalid conversion target kind=%d bits=%d", toKind, toBits)
				break
			}
			if err = checkTypes([]ValType{fromTy}); err != nil {
				break
			}
			next := append(popN(1), toTy)
			successor(fallthroughPC, next)
		case OpJump:
			if err = branch(int(instr.Arg), st.clone()); err != nil {
				break
			}
		case OpJumpIfZero, OpJumpIfNotZero:
			if err = checkDepth(1); err != nil {
				break
			}
			next := popN(1)
			if err = branch(int(instr.Arg), next); err != nil {
				break
			}
			successor(fallthroughPC, next)
		case OpCallV, OpCallN:
			var params, results []ValType
			if op == OpCallV {
				if instr.Arg < 0 || int(instr.Arg) >= len(p.Funcs) {
					err = verifyErrf(f, pc, "call to virtual function %d out of range [0,%d)", instr.Arg, len(p.Funcs))
					break
				}
				callee := p.Funcs[instr.Arg]
				params, results = callee.Params, callee.Results
			} else {
				if instr.Arg < 0 || int(instr.Arg) >= len(p.Natives) {
					err = verifyErrf(f, pc, "call to native function %d out of range [0,%d)", instr.Arg, len(p.Natives))
					break
				}
				callee := p.Natives[instr.Arg]
				params, results = callee.Params, callee.Results
			}
			if err = checkDepth(len(params)); err != nil {
				break
			}
			if err = checkTypes(params); err != nil {
				break
			}
			next := popN(len(params))
			next = append(next, results...)
			successor(fallthroughPC, next)
		case OpDispatch:
			if len(f.Dispatch) == 0 {
				err = verifyErrf(f, pc, "dispatch requires a dispatch table, but the function has none")
				break
			}
			if err = checkDepth(1); err != nil {
				break
			}
			if err = checkTypes([]ValType{TypeInt}); err != nil {
				break
			}
			// Every table entry is a potential target, so all of them must be
			// valid instruction boundaries and every target is a successor.
			next := popN(1)
			for _, target := range f.Dispatch {
				if err = branch(int(target), next); err != nil {
					break
				}
			}

		case OpReturn:
			n := int(instr.Arg)
			if n < 0 || n != len(f.Results) {
				err = verifyErrf(f, pc, "return of %d value(s), function declares %d", n, len(f.Results))
				break
			}
			if err = checkDepth(n); err != nil {
				break
			}
			if err = checkTypes(f.Results); err != nil {
				break
			}
			// Terminal: no successors.
		case OpHalt:
			// Terminal: no successors.
		case OpNop:
			successor(fallthroughPC, st.clone())
		default:
			eff, ok := op.Effect()
			if !ok {
				err = verifyErrf(f, pc, "unknown instruction")
				break
			}
			err = applyEffect(eff)
		}
		if err != nil {
			return err
		}

		if len(st) > MaxStackLimit {
			return verifyErrf(f, pc, "operand stack depth %d exceeds limit %d", len(st), MaxStackLimit)
		}
	}

	// Every instruction must be reachable or the program is malformed: an
	// unreachable instruction cannot have its stack effect checked, and the
	// emitted dispatcher would be dead code. Require full reachability.
	for i := range instrs {
		pc := i * InstrSize
		if _, ok := states[pc]; !ok {
			return verifyErrf(f, pc, "unreachable instruction (%s)", instrs[i].Op)
		}
	}

	// The last instruction must terminate the frame so the dispatcher can never
	// fall off the end of the code.
	last := instrs[len(instrs)-1]
	switch last.Op {
	case OpReturn, OpJump, OpDispatch, OpHalt:
	default:
		return verifyErrf(f, last.PC, "function does not end with a terminator (got %s)", last.Op)
	}

	f.MaxStack = maxStack
	return nil
}

// convertKindType maps a conversion kind and bit width to an abstract type.
func convertKindType(kind, bits int) (ValType, bool) {
	switch kind {
	case KindInt, KindUint:
		switch bits {
		case 8, 16, 32, 64:
			return TypeInt, true
		}
	case KindF32:
		if bits == 32 {
			return TypeFloat, true
		}
	case KindF64:
		if bits == 64 {
			return TypeFloat, true
		}
	}
	return TypeAny, false
}

// CheckAll is a convenience wrapper that verifies a program and, on failure,
// returns an error mentioning every problem found. The first problem is
// reported; later ones are appended as context for diagnostics.
func (p *Program) CheckAll() error {
	var errs []string
	for _, f := range p.Funcs {
		if err := p.verifyFunc(f); err != nil {
			errs = append(errs, err.Error())
		}
	}
	if len(errs) == 0 {
		return nil
	}
	return fmt.Errorf("%s", strings.Join(errs, "\n"))
}
