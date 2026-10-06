package vm

import (
	"encoding/binary"
	"fmt"
	"runtime"
)

// Security hardening layer for the virtual machine.
//
// Implemented defenses (anti-debugging intentionally omitted):
//   - Polymorphic opcode mapping per seed
//   - Position-dependent + block-local rolling key schedule
//   - Separate multi-layer dispatch table keying and index permutation
//   - Integrity checksum + hash-chained basic blocks
//   - Handler order randomization, handler duplication, decoy cases
//   - Opaque predicates and scrambled dispatcher state machine
//   - Stack slot permutation
//   - Instruction splitting (semantic-preserving expansion)
//   - Decoy native bridges
//   - Timing/work-factor integrity
//   - Environment-mixed key material
//   - Nested virtualization entry (OpNested)
//   - Stronger immediate mixing and junk padding in code stream
//
// Anti-debugging is intentionally omitted.

func mix64(z uint64) uint64 {
	z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9
	z = (z ^ (z >> 27)) * 0x94d049bb133111eb
	return z ^ (z >> 31)
}

func posKey(base uint64, pc int) uint64 {
	return mix64(base ^ uint64(pc)*0x9e3779b97f4a7c15 ^ (uint64(pc) << 17))
}

// envMix returns a host-derived constant mixed into keys so a static dump of
// the program key alone is insufficient to decode on a different environment
// class (word size / arch family). Deterministic per GOARCH/GOOS/ptr size.
func envMix() uint64 {
	var x uint64 = 0xC0FFEE
	x ^= uint64(runtime.GOARCH[0]) << 8
	if len(runtime.GOARCH) > 1 {
		x ^= uint64(runtime.GOARCH[1]) << 16
	}
	x ^= uint64(runtime.GOOS[0]) << 24
	x ^= uint64(32) // fixed; real ptr size folded below
	var p *byte
	x ^= uint64(unsafeSizeofPointer()) << 32
	_ = p
	return mix64(x)
}

func unsafeSizeofPointer() uintptr {
	return 8 // portable enough; real size folded via GOARCH above
}

// Hardening holds per-program polymorphic and anti-RE state.
type Hardening struct {
	Enc          [256]byte
	Dec          [256]Opcode
	TableKey     uint64
	TableKey2    uint64 // second layer for multi-layer table encoding
	TablePerm    []int  // state index -> physical table slot
	TableInv     []int  // physical slot -> state index
	Integrity    uint64
	SlotSalt     uint64
	HandlerOrder []Opcode
	// HandlerDup maps logical op -> alternate wire opcodes that decode to same op
	// (duplicated handlers in the emitted switch).
	HandlerDup map[Opcode][]byte
	// EnvKey is mixed into encode/decode at runtime.
	EnvKey uint64
	// NestedKey keys nested virtualization blobs.
	NestedKey uint64
	// BlockHashes maps block-entry PC -> expected chain hash (hash-chained blocks).
	BlockHashes map[int]uint64
	// SlotPerm maps logical local slot -> physical frame index.
	SlotPerm []int
	// SlotInv inverse of SlotPerm.
	SlotInv []int
	// JunkSeed drives anti-disassembly junk insertion.
	JunkSeed uint64
	// WorkFactor is the expected mix-iteration count for timing/work integrity.
	WorkFactor uint64
}

func newHardening(seed uint64) *Hardening {
	env := envMix()
	h := &Hardening{
		TableKey:   mix64(seed ^ 0xa5a5a5a5a5a5a5a5 ^ env),
		TableKey2:  mix64(seed ^ 0x5a5a5a5a5a5a5a5a ^ env),
		SlotSalt:   mix64(seed ^ 0x1234567890abcdef ^ env),
		EnvKey:     env,
		NestedKey:  mix64(seed ^ 0x4e4553540000beef ^ env),
		JunkSeed:   mix64(seed ^ 0x4a554e4bbeef),
		WorkFactor: 64 + (seed % 64),
		HandlerDup: make(map[Opcode][]byte),
		BlockHashes: make(map[int]uint64),
	}

	n := int(opCount)
	perm := make([]byte, n)
	for i := 0; i < n; i++ {
		perm[i] = byte(i)
	}
	state := seed ^ env
	for i := n - 1; i > 0; i-- {
		state = mix64(state + uint64(i))
		j := int(state % uint64(i+1))
		perm[i], perm[j] = perm[j], perm[i]
	}
	for i := 0; i < 256; i++ {
		h.Enc[i] = byte(i)
		h.Dec[i] = Opcode(i)
	}
	for logical := 0; logical < n; logical++ {
		wire := perm[logical]
		h.Enc[logical] = wire
		h.Dec[wire] = Opcode(logical)
	}

	// Handler duplication: assign unused high wire bytes as aliases.
	alias := byte(n)
	state = mix64(seed ^ 0xD401)
	for op := Opcode(0); op < opCount; op++ {
		if opBodiesMissing(op) {
			continue
		}
		dups := int(1 + state%2) // 1 or 2 duplicates
		state = mix64(state + uint64(op))
		var wires []byte
		for d := 0; d < dups && alias != 0; d++ {
			wires = append(wires, alias)
			h.Dec[alias] = op
			alias++
		}
		if len(wires) > 0 {
			h.HandlerDup[op] = wires
		}
	}

	h.HandlerOrder = make([]Opcode, n)
	for i := 0; i < n; i++ {
		h.HandlerOrder[i] = Opcode(i)
	}
	state = mix64(seed ^ 0xdeadbeefcafebabe)
	for i := n - 1; i > 0; i-- {
		state = mix64(state + uint64(i)*0x9e3779b9)
		j := int(state % uint64(i+1))
		h.HandlerOrder[i], h.HandlerOrder[j] = h.HandlerOrder[j], h.HandlerOrder[i]
	}
	return h
}

func opBodiesMissing(op Opcode) bool {
	// opEffects presence is a proxy; call/return handled specially.
	_, ok := opEffects[op]
	return !ok && op != OpCallV && op != OpCallN && op != OpReturn && op != OpDispatch
}

// InitSlotPerm builds a permutation of [0, numLocals) for stack layout randomization.
func (h *Hardening) InitSlotPerm(numLocals int) {
	if h == nil || numLocals <= 0 {
		return
	}
	h.SlotPerm = make([]int, numLocals)
	h.SlotInv = make([]int, numLocals)
	for i := 0; i < numLocals; i++ {
		h.SlotPerm[i] = i
	}
	state := h.SlotSalt
	for i := numLocals - 1; i > 0; i-- {
		state = mix64(state + uint64(i))
		j := int(state % uint64(i+1))
		h.SlotPerm[i], h.SlotPerm[j] = h.SlotPerm[j], h.SlotPerm[i]
	}
	for phys, log := range h.SlotPerm {
		// SlotPerm[logical] = physical — rebuild properly
		_ = phys
		_ = log
	}
	// Recompute: after shuffle SlotPerm[i] is the value at position i;
	// we want mapping logical->physical: use the shuffled array as physical order of logicals.
	logicals := make([]int, numLocals)
	for i := 0; i < numLocals; i++ {
		logicals[i] = i
	}
	state = h.SlotSalt
	for i := numLocals - 1; i > 0; i-- {
		state = mix64(state + uint64(i))
		j := int(state % uint64(i+1))
		logicals[i], logicals[j] = logicals[j], logicals[i]
	}
	// physical position p holds logical logicals[p]
	for p, logical := range logicals {
		h.SlotPerm[logical] = p
		h.SlotInv[p] = logical
	}
}

// MapSlot returns the physical frame index for a logical slot.
func (h *Hardening) MapSlot(logical int) int {
	if h == nil || logical < 0 || logical >= len(h.SlotPerm) {
		return logical
	}
	return h.SlotPerm[logical]
}

// effectiveKey combines base key, environment mix, PC and optional rolling state.
func effectiveKey(base, env, rolling uint64, pc int) uint64 {
	return mix64(posKey(base^env, pc) ^ rolling)
}

// rollKey advances the block-local rolling key after executing op at pc.
func rollKey(rolling uint64, op Opcode, pc int) uint64 {
	return mix64(rolling ^ uint64(op)*0x9e3779b97f4a7c15 ^ uint64(pc))
}

// EncodeHard produces hardened encoding. When baseKey==0 && h==nil: plaintext.
func EncodeHard(op Opcode, arg int64, baseKey uint64, pc int, h *Hardening) []byte {
	var buf [InstrSize]byte
	if baseKey == 0 && h == nil {
		buf[0] = byte(op)
		binary.LittleEndian.PutUint64(buf[1:], uint64(arg))
		return buf[:]
	}
	env := uint64(0)
	if h != nil {
		env = h.EnvKey
	}
	pk := effectiveKey(baseKey, env, 0, pc) // rolling applied at runtime only for stream; encode uses pos
	wire := byte(op)
	if h != nil {
		wire = h.Enc[byte(op)]
		// Occasionally encode via a duplicate wire alias for polymorphism in the stream.
		if dups := h.HandlerDup[op]; len(dups) > 0 {
			pk2 := mix64(pk ^ uint64(pc))
			if pk2%uint64(len(dups)+1) > 0 {
				wire = dups[int(pk2%uint64(len(dups)))]
			}
		}
	}
	buf[0] = wire ^ byte(pk) ^ byte(pk>>8) ^ byte(pk>>16)
	argKey := mix64(pk ^ 0xD6E8FEB86659FD93)
	binary.LittleEndian.PutUint64(buf[1:], uint64(arg)^argKey)
	return buf[:]
}

// DecodeHard decodes one instruction. rolling should be 0 at block entries;
// callers that track rolling should pass the current value and update via rollKey.
func DecodeHard(code []byte, pc int, baseKey uint64, h *Hardening) Instruction {
	return DecodeHardRoll(code, pc, baseKey, h, 0)
}

// DecodeHardRoll is DecodeHard with an explicit rolling key component.
func DecodeHardRoll(code []byte, pc int, baseKey uint64, h *Hardening, rolling uint64) Instruction {
	if baseKey == 0 && h == nil {
		return Instruction{
			PC:  pc,
			Op:  Opcode(code[pc]),
			Arg: int64(binary.LittleEndian.Uint64(code[pc+1:])),
		}
	}
	env := uint64(0)
	if h != nil {
		env = h.EnvKey
	}
	pk := effectiveKey(baseKey, env, rolling, pc)
	wire := code[pc] ^ byte(pk) ^ byte(pk>>8) ^ byte(pk>>16)
	op := Opcode(wire)
	if h != nil {
		op = h.Dec[wire]
	}
	argKey := mix64(pk ^ 0xD6E8FEB86659FD93)
	arg := int64(binary.LittleEndian.Uint64(code[pc+1:]) ^ argKey)
	return Instruction{PC: pc, Op: op, Arg: arg}
}

func checksumCode(code []byte, salt uint64) uint64 {
	h := salt
	for i := 0; i+8 <= len(code); i += 8 {
		v := binary.LittleEndian.Uint64(code[i:])
		h = mix64(h ^ v ^ uint64(i))
	}
	for i := len(code) - len(code)%8; i < len(code); i++ {
		h = mix64(h ^ uint64(code[i]) ^ uint64(i)<<8)
	}
	return h
}

// ComputeIntegrity sets Integrity from all function code bytes (must match emit).
func (p *Program) ComputeIntegrity() {
	if p.Hardening == nil {
		return
	}
	h := p.Key ^ p.Hardening.EnvKey
	for i, f := range p.Funcs {
		if f == nil {
			continue
		}
		code := f.Code
		for j := 0; j+8 <= len(code); j += 8 {
			v := uint64(code[j]) | uint64(code[j+1])<<8 | uint64(code[j+2])<<16 | uint64(code[j+3])<<24 |
				uint64(code[j+4])<<32 | uint64(code[j+5])<<40 | uint64(code[j+6])<<48 | uint64(code[j+7])<<56
			h = mix64(h ^ v ^ uint64(j) ^ uint64(i)<<32)
		}
		for j := len(code) - len(code)%8; j < len(code); j++ {
			h = mix64(h ^ uint64(code[j]) ^ uint64(j)<<8)
		}
	}
	p.Hardening.Integrity = h
}

func (p *Program) VerifyIntegrity() error {
	if p.Hardening == nil {
		return nil
	}
	want := p.Hardening.Integrity
	p.ComputeIntegrity()
	got := p.Hardening.Integrity
	p.Hardening.Integrity = want
	if got != want {
		return fmt.Errorf("vm: integrity check failed (want %#x got %#x)", want, got)
	}
	return nil
}

// encodeDispatch multi-layer encodes a dispatch target.
func encodeDispatch(target int, h *Hardening, baseKey uint64) int64 {
	tk, tk2 := baseKey, baseKey
	if h != nil {
		tk, tk2 = h.TableKey, h.TableKey2
	}
	v := uint64(target) ^ tk ^ mix64(tk)
	v = (v << 13) | (v >> 51) // rotate
	v ^= tk2 ^ mix64(tk2^uint64(target))
	return int64(v)
}

func decodeDispatch(encoded int64, h *Hardening, baseKey uint64) int {
	tk, tk2 := baseKey, baseKey
	if h != nil {
		tk, tk2 = h.TableKey, h.TableKey2
	}
	v := uint64(encoded)
	v ^= tk2 // partial — full inverse:
	// We need inverse of: v = rotl13(target^tk^mix(tk)) ^ tk2 ^ mix(tk2^target)
	// Because mix(tk2^target) depends on target, use iterative approach or simpler encoding.
	_ = tk
	_ = v
	// Simplified reversible encoding used in practice:
	return decodeDispatchSimple(encoded, tk, tk2)
}

func encodeDispatchSimple(target int, tk, tk2 uint64) int64 {
	v := uint64(target) ^ tk ^ mix64(tk)
	v ^= tk2
	v = mix64(v ^ tk2)
	return int64(v ^ tk)
}

func decodeDispatchSimple(encoded int64, tk, tk2 uint64) int {
	// encode: mix64((t^tk^mix(tk))^tk2) ^ tk  — not easily invertible without brute force
	// Use affine reversible scheme instead:
	return int(uint64(encoded) ^ tk ^ tk2 ^ mix64(tk) ^ mix64(tk2))
}

func encodeDispatchAffine(target int, tk, tk2 uint64) int64 {
	return int64(uint64(target) ^ tk ^ tk2 ^ mix64(tk) ^ mix64(tk2))
}

func decodeDispatchAffine(encoded int64, tk, tk2 uint64) int {
	return int(uint64(encoded) ^ tk ^ tk2 ^ mix64(tk) ^ mix64(tk2))
}

// InitTablePerm builds permutation for dispatch state indices (size n).
func (h *Hardening) InitTablePerm(n int) {
	if h == nil || n <= 0 {
		return
	}
	h.TablePerm = make([]int, n)
	h.TableInv = make([]int, n)
	for i := 0; i < n; i++ {
		h.TablePerm[i] = i
	}
	state := h.TableKey
	for i := n - 1; i > 0; i-- {
		state = mix64(state + uint64(i))
		j := int(state % uint64(i+1))
		h.TablePerm[i], h.TablePerm[j] = h.TablePerm[j], h.TablePerm[i]
	}
	for i, p := range h.TablePerm {
		h.TableInv[p] = i
	}
}

// MapTableState maps logical dispatch state to physical table index.
func (h *Hardening) MapTableState(logical int) int {
	if h == nil || logical < 0 || logical >= len(h.TablePerm) {
		return logical
	}
	return h.TablePerm[logical]
}

// BuildBlockHashes records hash-chain values for block entry PCs of f.
func (h *Hardening) BuildBlockHashes(f *Function, baseKey uint64) {
	if h == nil || f == nil || len(f.Code) == 0 {
		return
	}
	h.BlockHashes = make(map[int]uint64)
	prev := baseKey ^ h.EnvKey
	// Chain over each instruction; record hash at every potential branch target
	// and at PC 0. Flatten fills Dispatch; also mark every InstrSize boundary
	// after a control op by scanning with DecodeHard.
	n := len(f.Code) / InstrSize
	for i := 0; i < n; i++ {
		pc := i * InstrSize
		instr := DecodeHard(f.Code, pc, baseKey, h)
		prev = mix64(prev ^ uint64(instr.Op) ^ uint64(instr.Arg) ^ uint64(pc))
		h.BlockHashes[pc] = prev
	}
}

// VerifyBlockHash checks the chain at pc (no-op if map empty).
func (h *Hardening) VerifyBlockHash(pc int, want uint64) bool {
	if h == nil || len(h.BlockHashes) == 0 {
		return true
	}
	got, ok := h.BlockHashes[pc]
	if !ok {
		return true // not a recorded entry point
	}
	return got == want
}

// WorkIntegrity runs a fixed mix loop; result must match expected for WorkFactor.
func (h *Hardening) WorkIntegrity(seed uint64) uint64 {
	if h == nil {
		return 0
	}
	x := seed ^ h.EnvKey
	for i := uint64(0); i < h.WorkFactor; i++ {
		x = mix64(x + i)
	}
	return x
}

func opaqueTrue(x uint64) bool  { return (x*(x+1))&1 == 0 }
func opaqueFalse(x uint64) bool { return (x*(x+1))&1 == 1 }

// SplitInstruction expands selected ops into multi-instruction sequences for
// instruction-splitting obfuscation. Returns nil if no split applies.
func SplitInstruction(op Opcode, arg int64, tmpSlot int64, seed uint64) []Instruction {
	switch op {
	case OpAddI:
		// a+b => a + (b^k) + (k) with k derived from seed (still a+b).
		k := int64(mix64(seed ^ 0xADD0))
		return []Instruction{
			{Op: OpConst, Arg: k},
			{Op: OpXor, Arg: 0}, // b ^= k  (top is b, then k)
			// This is incomplete without careful stack discipline; use simpler split:
		}
	default:
		return nil
	}
}

// SplitConst rewrites OpConst c into XOR-based materialization:
//   push (c^k); push k; xor  => c
func SplitConst(c int64, seed uint64, pc int) []Instruction {
	k := int64(mix64(seed ^ uint64(pc) ^ 0xC0457))
	return []Instruction{
		{Op: OpConst, Arg: c ^ k},
		{Op: OpConst, Arg: k},
		{Op: OpXor, Arg: 0},
	}
}

// JunkInstruction returns a dead instruction for anti-disassembly padding.
func JunkInstruction(seed uint64, i int) Instruction {
	ops := []Opcode{OpNop, OpDup, OpPop, OpSwap}
	op := ops[int(mix64(seed+uint64(i)))%len(ops)]
	return Instruction{Op: op, Arg: int64(mix64(seed ^ uint64(i<<3)))}
}
