// Package vm implements garble's stack-based virtualization engine.
//
// A Go function eligible for virtualization has its body lowered to a compact
// bytecode program (see compile.go). The bytecode is a genuine stack machine:
// every instruction consumes operands from the top of a virtual operand stack
// and pushes its results back. The same program can be executed two ways:
//
//   - Interpreter (exec.go) - used by tests, by the semantic equivalence
//     checker and by tooling.
//   - Emitted Go source (emit.go) - a specialized copy of the dispatch loop is
//     written into the obfuscated package, so the shipped binary runs the
//     bytecode without ever containing the original native instructions.
//
// Both paths implement the exact semantics documented here. Any divergence
// between them is a bug; TestInterpreterMatchesEmitted guards against it.
//
// # Value model
//
// Every value on the operand stack occupies exactly one 8-byte word:
//
//   - Signed and unsigned integers are stored as their two's-complement bit
//     pattern in the word.
//   - float64 is stored as its IEEE-754 bit pattern.
//   - float32 is stored as its IEEE-754 bit pattern in the low 32 bits.
//   - Booleans are stored as the words 0 (false) and 1 (true).
//
// The VM deliberately never stores a Go pointer, interface, slice, map, string
// or channel in a stack word. Those types are outside the supported subset
// precisely so that the operand stack stays invisible to the garbage collector
// and can never be mistaken for a live pointer root. See docs/VIRTUALIZATION.md.
package vm

import "fmt"

// Opcode identifies a single virtual machine instruction.
type Opcode uint8

// The virtual instruction set. Each instruction is documented in opDocs.
const (
	// OpNop does nothing.
	OpNop Opcode = iota
	// OpConst pushes the operand as an integer word.
	OpConst
	// OpConstF pushes the operand as a floating point word. It is distinct from
	// OpConst so that the verifier can type the pushed word without extra
	// per-instruction metadata.
	OpConstF
	// OpPop discards the top word.
	OpPop
	// OpDup duplicates the top word.
	OpDup
	// OpSwap exchanges the top two words.
	OpSwap
	// OpLoadLocal pushes locals[operand].
	OpLoadLocal
	// OpStoreLocal pops the top word into locals[operand].
	OpStoreLocal

	// Signed integer arithmetic.
	OpAddI
	OpSubI
	OpMulI
	OpDivI
	OpRemI
	OpNegI
	// OpDivU and OpRemU are the unsigned counterparts of OpDivI and OpRemI.
	// Go defines integer division differently for signed and unsigned operands,
	// so the compiler must select the correct one from the operand's type.
	OpDivU
	OpRemU

	// Bitwise and shift operations.
	OpAnd
	OpOr
	OpXor
	OpNot
	OpShl
	OpShr
	OpShrU

	// Floating point arithmetic.
	OpAddF
	OpSubF
	OpMulF
	OpDivF
	OpNegF

	// Signed integer comparisons; push 0 or 1.
	OpEqI
	OpNeI
	OpLtI
	OpLeI
	OpGtI
	OpGeI

	// Unsigned integer comparisons; push 0 or 1.
	OpLtU
	OpLeU
	OpGtU
	OpGeU

	// Floating point comparisons; push 0 or 1.
	OpEqF
	OpNeF
	OpLtF
	OpLeF
	OpGtF
	OpGeF

	// OpNotB is boolean negation: it maps 0 to 1 and 1 to 0.
	OpNotB

	// OpConvert reinterprets the top word according to the operand, which is
	// packed by MakeConvertOperand.
	OpConvert

	// OpJump sets the instruction pointer to operand.
	OpJump
	// OpJumpIfZero pops a word and jumps to operand when it is zero.
	OpJumpIfZero
	// OpJumpIfNotZero pops a word and jumps to operand when it is non-zero.
	OpJumpIfNotZero

	// OpCallV calls virtual function operand, transferring control between
	// bytecode and bytecode.
	OpCallV
	// OpCallN calls native function operand, transferring control between
	// bytecode and ordinary Go code.
	OpCallN

	// OpReturn returns operand results from the top of the stack.
	OpReturn

	// OpDispatch pops a state word and transfers control to the block recorded
	// for that state in the function's dispatch table. It is the machine's only
	// indirect branch: the target is data rather than an operand, so recovering
	// the control-flow graph of a flattened function requires decoding the
	// table as well as the code. Control-flow flattening rewrites every branch
	// of a function into a dispatcher in this form.
	OpDispatch

	// OpRemF is floating-point remainder (math.Mod semantics).
	OpRemF

	// OpNested runs a nested virtualization blob (secondary interpreter frame)
	// addressed by operand index into Program.Nested.
	OpNested

	// OpHalt stops the machine, returning the current stack.
	OpHalt
)

var opNames = map[Opcode]string{
	OpNop:           "NOP",
	OpConst:         "CONST",
	OpConstF:        "CONSTF",
	OpPop:           "POP",
	OpDup:           "DUP",
	OpSwap:          "SWAP",
	OpLoadLocal:     "LOAD",
	OpStoreLocal:    "STORE",
	OpAddI:          "ADD",
	OpSubI:          "SUB",
	OpMulI:          "MUL",
	OpDivI:          "DIV",
	OpRemI:          "REM",
	OpNegI:          "NEG",
	OpDivU:          "DIVU",
	OpRemU:          "REMU",
	OpAnd:           "AND",
	OpOr:            "OR",
	OpXor:           "XOR",
	OpNot:           "NOT",
	OpShl:           "SHL",
	OpShr:           "SHR",
	OpShrU:          "SHRU",
	OpAddF:          "ADDF",
	OpSubF:          "SUBF",
	OpMulF:          "MULF",
	OpDivF:          "DIVF",
	OpNegF:          "NEGF",
	OpRemF:          "REMF",
	OpNested:        "NESTED",
	OpEqI:           "EQI",
	OpNeI:           "NEI",
	OpLtI:           "LTI",
	OpLeI:           "LEI",
	OpGtI:           "GTI",
	OpGeI:           "GEI",
	OpLtU:           "LTU",
	OpLeU:           "LEU",
	OpGtU:           "GTU",
	OpGeU:           "GEU",
	OpEqF:           "EQF",
	OpNeF:           "NEF",
	OpLtF:           "LTF",
	OpLeF:           "LEF",
	OpGtF:           "GTF",
	OpGeF:           "GEF",
	OpNotB:          "NOTB",
	OpConvert:       "CONV",
	OpJump:          "JMP",
	OpJumpIfZero:    "JZ",
	OpJumpIfNotZero: "JNZ",
	OpCallV:         "CALLV",
	OpCallN:         "CALLN",
	OpReturn:        "RET",
	OpDispatch:      "DISPATCH",
	OpHalt:          "HALT",
}

// String returns the mnemonic of op, or a placeholder for an unknown opcode.
func (op Opcode) String() string {
	if name, ok := opNames[op]; ok {
		return name
	}
	return fmt.Sprintf("OP?%d", uint8(op))
}

// ValType is the abstract type of a word on the operand stack. It is used only
// by the verifier; the machine itself treats every word as an opaque uint64.
type ValType uint8

const (
	// TypeAny is the top of the type lattice: it unifies with everything.
	TypeAny ValType = iota
	// TypeInt covers signed and unsigned integers and booleans.
	TypeInt
	// TypeFloat covers float32 and float64.
	TypeFloat
)

func (t ValType) String() string {
	switch t {
	case TypeAny:
		return "any"
	case TypeInt:
		return "int"
	case TypeFloat:
		return "float"
	}
	return fmt.Sprintf("type?%d", uint8(t))
}

// join returns the least upper bound of two abstract types. Any is the top
// element, so joining anything with Any yields Any.
func (t ValType) join(other ValType) ValType {
	if t == other {
		return t
	}
	return TypeAny
}

// stackEffect describes how an instruction changes the operand stack.
type stackEffect struct {
	// pop is the number of words consumed from the top of the stack.
	pop int
	// push is the number of words produced on top of the stack.
	push int
	// popTy lists the required types of the consumed words in push order: the
	// first entry describes the deepest word of the group, the last entry the
	// top of stack. Its length must equal pop. TypeAny accepts any value.
	popTy []ValType
	// pushTy is the type of the produced word, when push is 1.
	pushTy ValType
}

var intBinOp = stackEffect{pop: 2, push: 1, popTy: []ValType{TypeInt, TypeInt}, pushTy: TypeInt}
var intUnOp = stackEffect{pop: 1, push: 1, popTy: []ValType{TypeInt}, pushTy: TypeInt}
var floatBinOp = stackEffect{pop: 2, push: 1, popTy: []ValType{TypeFloat, TypeFloat}, pushTy: TypeFloat}
var floatUnOp = stackEffect{pop: 1, push: 1, popTy: []ValType{TypeFloat}, pushTy: TypeFloat}
var cmpIntOp = stackEffect{pop: 2, push: 1, popTy: []ValType{TypeInt, TypeInt}, pushTy: TypeInt}
var cmpFloatOp = stackEffect{pop: 2, push: 1, popTy: []ValType{TypeFloat, TypeFloat}, pushTy: TypeInt}

// opEffects maps every fixed-arity instruction to its stack effect. Instructions
// whose arity depends on program metadata (OpCallV, OpCallN, OpReturn) are
// absent and are resolved by the verifier.
var opEffects = map[Opcode]stackEffect{
	OpNop:        {},
	OpConst:      {pop: 0, push: 1, pushTy: TypeInt},
	OpConstF:     {pop: 0, push: 1, pushTy: TypeFloat},
	OpPop:        {pop: 1, push: 0, popTy: []ValType{TypeAny}},
	OpDup:        {pop: 0, push: 1, popTy: []ValType{TypeAny}, pushTy: TypeAny},
	OpSwap:       {pop: 2, push: 2, popTy: []ValType{TypeAny, TypeAny}},
	OpLoadLocal:  {pop: 0, push: 1, pushTy: TypeAny},
	OpStoreLocal: {pop: 1, push: 0, popTy: []ValType{TypeAny}},

	OpAddI: intBinOp, OpSubI: intBinOp, OpMulI: intBinOp,
	OpDivI: intBinOp, OpRemI: intBinOp,
	OpDivU: intBinOp, OpRemU: intBinOp,
	OpNegI: intUnOp,

	OpAnd: intBinOp, OpOr: intBinOp, OpXor: intBinOp,
	OpNot: intUnOp,
	OpShl: intBinOp, OpShr: intBinOp, OpShrU: intBinOp,

	OpAddF: floatBinOp, OpSubF: floatBinOp, OpMulF: floatBinOp,
	OpDivF: floatBinOp, OpRemF: floatBinOp, OpNegF: floatUnOp,

	OpEqI: cmpIntOp, OpNeI: cmpIntOp, OpLtI: cmpIntOp,
	OpLeI: cmpIntOp, OpGtI: cmpIntOp, OpGeI: cmpIntOp,
	OpLtU: cmpIntOp, OpLeU: cmpIntOp, OpGtU: cmpIntOp, OpGeU: cmpIntOp,

	OpEqF: cmpFloatOp, OpNeF: cmpFloatOp, OpLtF: cmpFloatOp,
	OpLeF: cmpFloatOp, OpGtF: cmpFloatOp, OpGeF: cmpFloatOp,

	OpNotB:    {pop: 1, push: 1, popTy: []ValType{TypeInt}, pushTy: TypeInt},
	OpConvert: {pop: 1, push: 1, popTy: []ValType{TypeAny}, pushTy: TypeAny},

	OpJump:          {},
	OpJumpIfZero:    {pop: 1, push: 0, popTy: []ValType{TypeAny}},
	OpJumpIfNotZero: {pop: 1, push: 0, popTy: []ValType{TypeAny}},

	OpNested: {pop: 0, push: 0},
	OpHalt: {},
}

// Effect returns the fixed stack effect of op. The second result is false for
// instructions whose stack effect depends on program metadata.
func (op Opcode) Effect() (stackEffect, bool) {
	eff, ok := opEffects[op]
	return eff, ok
}

// opDocs documents every instruction: operands, stack effect and failure modes.
// It is the normative reference for the instruction set and is surfaced by the
// disassembler and the generated documentation.
var opDocs = map[Opcode]string{
	OpNop:           "operands: none; stack: -> ; never fails",
	OpConst:         "operands: word; stack: -> v; never fails",
	OpConstF:        "operands: word; stack: -> v; pushes a float word; never fails",
	OpPop:           "operands: none; stack: v -> ; requires depth >= 1",
	OpDup:           "operands: none; stack: v -> v v; requires depth >= 1",
	OpSwap:          "operands: none; stack: a b -> b a; requires depth >= 2",
	OpLoadLocal:     "operands: slot; stack: -> locals[slot]; requires slot < numLocals",
	OpStoreLocal:    "operands: slot; stack: v -> ; requires slot < numLocals and depth >= 1",
	OpAddI:          "operands: none; stack: a b -> a+b (wrapping); requires depth >= 2",
	OpSubI:          "operands: none; stack: a b -> a-b (wrapping); requires depth >= 2",
	OpMulI:          "operands: none; stack: a b -> a*b (wrapping); requires depth >= 2",
	OpDivI:          "operands: none; stack: a b -> a/b; panics on b == 0, as Go does",
	OpRemI:          "operands: none; stack: a b -> a%b; panics on b == 0, as Go does",
	OpNegI:          "operands: none; stack: a -> -a; requires depth >= 1",
	OpDivU:          "operands: none; stack: a b -> a/b unsigned; panics on b == 0, as Go does",
	OpRemU:          "operands: none; stack: a b -> a%b unsigned; panics on b == 0, as Go does",
	OpAnd:           "operands: none; stack: a b -> a&b; requires depth >= 2",
	OpOr:            "operands: none; stack: a b -> a|b; requires depth >= 2",
	OpXor:           "operands: none; stack: a b -> a^b; requires depth >= 2",
	OpNot:           "operands: none; stack: a -> ^a; requires depth >= 1",
	OpShl:           "operands: none; stack: a n -> a<<n; Go shift semantics for n >= 64",
	OpShr:           "operands: none; stack: a n -> a>>n (arithmetic); Go semantics",
	OpShrU:          "operands: none; stack: a n -> a>>n (logical); Go semantics",
	OpAddF:          "operands: none; stack: a b -> a+b (float64); requires depth >= 2",
	OpSubF:          "operands: none; stack: a b -> a-b (float64); requires depth >= 2",
	OpMulF:          "operands: none; stack: a b -> a*b (float64); requires depth >= 2",
	OpDivF:          "operands: none; stack: a b -> a/b (float64); division by zero yields Inf/NaN",
	OpNegF:          "operands: none; stack: a -> -a (float64); requires depth >= 1",
	OpRemF:          "operands: none; stack: a b -> math.Mod(a,b); requires depth >= 2",
	OpEqI:           "operands: none; stack: a b -> (a==b); requires depth >= 2",
	OpNeI:           "operands: none; stack: a b -> (a!=b); requires depth >= 2",
	OpLtI:           "operands: none; stack: a b -> (a<b) signed; requires depth >= 2",
	OpLeI:           "operands: none; stack: a b -> (a<=b) signed; requires depth >= 2",
	OpGtI:           "operands: none; stack: a b -> (a>b) signed; requires depth >= 2",
	OpGeI:           "operands: none; stack: a b -> (a>=b) signed; requires depth >= 2",
	OpLtU:           "operands: none; stack: a b -> (a<b) unsigned; requires depth >= 2",
	OpLeU:           "operands: none; stack: a b -> (a<=b) unsigned; requires depth >= 2",
	OpGtU:           "operands: none; stack: a b -> (a>b) unsigned; requires depth >= 2",
	OpGeU:           "operands: none; stack: a b -> (a>=b) unsigned; requires depth >= 2",
	OpEqF:           "operands: none; stack: a b -> (a==b) float; NaN != NaN holds",
	OpNeF:           "operands: none; stack: a b -> (a!=b) float; NaN != NaN holds",
	OpLtF:           "operands: none; stack: a b -> (a<b) float; false when NaN",
	OpLeF:           "operands: none; stack: a b -> (a<=b) float; false when NaN",
	OpGtF:           "operands: none; stack: a b -> (a>b) float; false when NaN",
	OpGeF:           "operands: none; stack: a b -> (a>=b) float; false when NaN",
	OpNotB:          "operands: none; stack: v -> 1-v; requires v be 0 or 1",
	OpConvert:       "operands: packed conversion; stack: v -> converted v",
	OpJump:          "operands: target; stack: -> ; target must be an instruction boundary",
	OpJumpIfZero:    "operands: target; stack: v -> ; requires depth >= 1",
	OpJumpIfNotZero: "operands: target; stack: v -> ; requires depth >= 1",
	OpCallV:         "operands: function index; stack: args -> results; arity from callee signature",
	OpCallN:         "operands: native index; stack: args -> results; arity from native signature",
	OpReturn:        "operands: result count n; stack: r0..rn-1 -> ; terminates the frame",
	OpDispatch:      "operands: none; stack: state -> ; jumps to dispatchTable[state]; requires a dispatch table and state < len(dispatchTable)",
	OpNested:        "operands: blob index; runs nested bytecode blob; stack effect depends on blob",
	OpHalt:          "operands: none; stack: -> ; terminates the machine",
}

// Doc returns the reference documentation for op.
func (op Opcode) Doc() string {
	if doc, ok := opDocs[op]; ok {
		return doc
	}
	return "unknown instruction"
}
