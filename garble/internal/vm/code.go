package vm

import (
	"fmt"
	"strings"
)

// InstrSize is the encoded size of one virtual instruction: a single opcode
// byte followed by a little-endian int64 operand. The encoding is deliberately
// fixed width so that any offset that is a multiple of InstrSize is a valid
// instruction boundary, which makes branch target validation a simple
// divisibility and range check.
const InstrSize = 9

// Function is one virtualized function: its signature, its frame layout and its
// encoded bytecode.
type Function struct {
	// Name is a descriptive name used in disassembly and diagnostics. It is not
	// referenced by the emitted program.
	Name string
	// Params and Results describe the virtual calling convention. Every value
	// is one word; the kinds are informational and drive native bridging.
	Params  []ValType
	Results []ValType
	// NumLocals is the size of the virtual frame, in words. Parameters occupy
	// the first len(Params) slots.
	NumLocals int
	// LocalTypes gives the abstract type of every frame slot. Its length is
	// NumLocals. Slots holding a value that is never read may be TypeAny.
	LocalTypes []ValType
	// MaxStack is the verified maximum operand stack depth, relative to entry.
	MaxStack int
	// Dispatch, when non-nil, is the function's indirect branch table: the
	// state word popped by OpDispatch indexes it and each entry is the byte
	// offset of the instruction to jump to. Control-flow flattening produces
	// it. A function that is not flattened leaves it nil and contains no
	// OpDispatch instruction.
	Dispatch []int32
	// Code is the encoded instruction stream.
	Code []byte
}

// NumInstrs reports how many instructions the function contains.
func (f *Function) NumInstrs() int { return len(f.Code) / InstrSize }

// NativeFunc describes a real Go function that bytecode can call. Calls to
// native functions are the only boundary where control leaves the virtual
// machine and re-enters ordinary Go code.
type NativeFunc struct {
	// GoName is the identifier to call in the generated package. The caller is
	// responsible for resolving it (including any obfuscated name).
	GoName string
	// Params and Results are the word-level signature seen by the bytecode.
	Params  []ValType
	Results []ValType
	// Bridge is the body of the generated Go function that converts words to
	// the callee's real parameter types, performs the call, and converts the
	// results back to words. It is produced by the SSA compiler, which is the
	// only place that knows the real types and import names.
	Bridge string
}

// Arity reports how many words the native function consumes from the stack.
func (n *NativeFunc) Arity() int { return len(n.Params) }

// Program is a complete virtualized unit: a set of virtual functions sharing
// one instruction set, one dispatch loop and one native function table.
type Program struct {
	// Key is the base secret for position-dependent instruction encoding.
	// Combined with Hardening it yields polymorphic, PC-keyed bytecode.
	Key uint64
	// Hardening holds per-build opcode permutation, table key, integrity and
	// handler order. Nil means legacy plain XOR encoding (tests may omit it).
	Hardening *Hardening
	// Funcs are the virtual functions, indexed by the operand of OpCallV.
	Funcs []*Function
	// Natives are the native functions, indexed by the operand of OpCallN.
	Natives []*NativeFunc
	// Nested holds secondary bytecode blobs for OpNested (nested virtualization).
	Nested [][]byte
	// DecoyNatives are never-called native stubs that exist only to mislead analysis.
	DecoyNatives []*NativeFunc

	// nativeImpl, when set, lets the interpreter call real Go functions for
	// OpCallN. The emitted program binds these at compile time instead; the
	// hook exists so tests can run programs that call out to native code.
	nativeImpl func(index int, args []uint64) []uint64
}

// BindNatives installs the callback used by the interpreter for OpCallN. It is
// not needed to execute programs that never call native functions.
func (p *Program) BindNatives(impl func(index int, args []uint64) []uint64) {
	p.nativeImpl = impl
}

// Instruction is a decoded instruction.
type Instruction struct {
	// PC is the byte offset of the instruction in the function's code.
	PC  int
	Op  Opcode
	Arg int64
}

// Encode produces a legacy single-key encoding. Prefer EncodeHard for hardened builds.
func Encode(op Opcode, arg int64, key uint64) []byte {
	return EncodeHard(op, arg, key, 0, nil)
}

// DecodeInstruction decodes with legacy single-key encoding at pc=0 subkey.
// Prefer DecodeHard when Hardening is present.
func DecodeInstruction(code []byte, pc int, key uint64) Instruction {
	return DecodeHard(code, pc, key, nil)
}

// Builder assembles a function body. Instructions are collected in decoded form
// and encoded once the program key is known.
type Builder struct {
	instrs []Instruction
}

// NewBuilder returns an empty Builder.
func NewBuilder() *Builder { return &Builder{} }

// Emit appends an instruction and returns the byte offset at which it will be
// encoded. Branch targets are expressed in these offsets.
func (b *Builder) Emit(op Opcode, arg int64) int {
	pc := len(b.instrs) * InstrSize
	b.instrs = append(b.instrs, Instruction{PC: pc, Op: op, Arg: arg})
	return pc
}

// Patch rewrites the operand of the instruction previously emitted at pc.
func (b *Builder) Patch(pc int, arg int64) {
	idx := pc / InstrSize
	if pc%InstrSize != 0 || idx < 0 || idx >= len(b.instrs) {
		panic("vm: patch of invalid instruction offset")
	}
	b.instrs[idx].Arg = arg
}

// Len reports the encoded length of the assembled body, in bytes.
func (b *Builder) Len() int { return len(b.instrs) * InstrSize }

// Instructions returns the assembled instructions in decoded form.
func (b *Builder) Instructions() []Instruction { return b.instrs }

// Encode encodes the assembled body under key using position-dependent
// hardening when h is non-nil.
func (b *Builder) Encode(key uint64) []byte {
	return b.EncodeHard(key, nil)
}

// EncodeHard encodes with full hardening (polymorphic opcodes + PC keys).
func (b *Builder) EncodeHard(key uint64, h *Hardening) []byte {
	out := make([]byte, 0, len(b.instrs)*InstrSize)
	for _, instr := range b.instrs {
		out = append(out, EncodeHard(instr.Op, instr.Arg, key, instr.PC, h)...)
	}
	return out
}

// Disassemble renders an encoded body as human-readable text.
func Disassemble(code []byte, key uint64) string {
	return DisassembleHard(code, key, nil)
}

// DisassembleHard renders code using the given hardening tables.
func DisassembleHard(code []byte, key uint64, h *Hardening) string {
	var sb strings.Builder
	for pc := 0; pc < len(code); pc += InstrSize {
		instr := DecodeHard(code, pc, key, h)
		fmt.Fprintf(&sb, "%04d  %-6s %d\n", pc, instr.Op, instr.Arg)
	}
	return sb.String()
}

// Disassemble renders the function as human-readable text.
func (f *Function) Disassemble(key uint64) string {
	var sb strings.Builder
	fmt.Fprintf(&sb, "func %s(%v) %v  locals=%d maxstack=%d\n",
		f.Name, f.Params, f.Results, f.NumLocals, f.MaxStack)
	if len(f.Dispatch) > 0 {
		fmt.Fprintf(&sb, "dispatch table (%d entries): %v\n", len(f.Dispatch), f.Dispatch)
	}
	sb.WriteString(Disassemble(f.Code, key))
	return sb.String()
}

// Disassemble renders the whole program as human-readable text.
func (p *Program) Disassemble() string {
	var sb strings.Builder
	for i, f := range p.Funcs {
		fmt.Fprintf(&sb, "=== virtual function %d ===\n", i)
		sb.WriteString(f.Disassemble(p.Key))
	}
	for i, n := range p.Natives {
		fmt.Fprintf(&sb, "=== native %d: %s(%v) %v ===\n", i, n.GoName, n.Params, n.Results)
	}
	return sb.String()
}
