package vm

import (
	"fmt"
	"math"
)

// maxCallDepth bounds the virtual call stack so that malformed or runaway
// bytecode fails with a clear error instead of exhausting host memory.
const maxCallDepth = 10000

// ExecutionError reports a runtime failure of the interpreter that is not a Go
// panic raised by the interpreted code itself (for example a malformed operand
// or a stack underflow that verification should have prevented).
type ExecutionError struct {
	Func string
	PC   int
	Msg  string
}

func (e *ExecutionError) Error() string {
	return fmt.Sprintf("vm: execute %s at %04d: %s", e.Func, e.PC, e.Msg)
}

type frame struct {
	fn     *Function
	locals []uint64
	retPC  int
	retFn  int // -1 for the entry frame
}

// Run executes the program's entry function (Funcs[0]) with the given arguments
// and returns the words it produced.
//
// Arguments are pushed in order, so the last argument is on top of the stack,
// matching the calling convention used by OpCallV and by the emitted code.
//
// Run never recovers panics raised by interpreted code: an integer division by
// zero or a nil dereference inside a native call propagates to the caller
// exactly as it would in the original program.
func (p *Program) Run(args ...uint64) ([]uint64, error) {
	if len(p.Funcs) == 0 {
		return nil, fmt.Errorf("vm: program has no functions")
	}
	return p.RunFunc(0, args...)
}

// RunFunc executes the virtual function at index fn with the given arguments.
func (p *Program) RunFunc(fn int, args ...uint64) ([]uint64, error) {
	if fn < 0 || fn >= len(p.Funcs) {
		return nil, fmt.Errorf("vm: function index %d out of range", fn)
	}
	entry := p.Funcs[fn]
	if len(args) != len(entry.Params) {
		return nil, fmt.Errorf("vm: %s expects %d argument(s), got %d", entry.Name, len(entry.Params), len(args))
	}
	if err := p.VerifyIntegrity(); err != nil {
		return nil, err
	}

	// Arguments are delivered through the frame, not through the operand
	// stack: the stack starts empty and parameters live in locals[0:len(args)],
	// matching the emitted runtime exactly.
	stack := make([]uint64, 0, 32)

	locals := make([]uint64, entry.NumLocals)
	copy(locals, args)
	workState := p.Key
	if p.Hardening != nil {
		workState = p.Hardening.WorkIntegrity(p.Key)
		// Apply slot permutation: args already in logical order; remap to physical.
	}

	cur := entry
	pc := 0
	var frames []frame

	pop := func(n int) ([]uint64, error) {
		if len(stack) < n {
			return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: fmt.Sprintf("stack underflow: need %d, have %d", n, len(stack))}
		}
		out := stack[len(stack)-n:]
		stack = stack[:len(stack)-n]
		return out, nil
	}

	for {
		if pc%InstrSize != 0 || pc < 0 || pc >= len(cur.Code) {
			return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: "instruction pointer out of range"}
		}
		instr := DecodeHard(cur.Code, pc, p.Key, p.Hardening)
		nextPC := pc + InstrSize
		if p.Hardening != nil {
			workState = rollKey(workState, instr.Op, pc)
		}

		switch instr.Op {
		case OpNop:
		case OpConst, OpConstF:
			stack = append(stack, uint64(instr.Arg))
		case OpPop:
			if _, err := pop(1); err != nil {
				return nil, err
			}
		case OpDup:
			if len(stack) < 1 {
				return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: "stack underflow"}
			}
			stack = append(stack, stack[len(stack)-1])
		case OpSwap:
			if len(stack) < 2 {
				return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: "stack underflow"}
			}
			stack[len(stack)-1], stack[len(stack)-2] = stack[len(stack)-2], stack[len(stack)-1]
		case OpLoadLocal:
			if instr.Arg < 0 || int(instr.Arg) >= len(locals) {
				return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: "local load out of range"}
			}
			stack = append(stack, locals[instr.Arg])
		case OpStoreLocal:
			if instr.Arg < 0 || int(instr.Arg) >= len(locals) {
				return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: "local store out of range"}
			}
			v, err := pop(1)
			if err != nil {
				return nil, err
			}
			locals[instr.Arg] = v[0]

		case OpAddI, OpSubI, OpMulI, OpDivI, OpRemI, OpDivU, OpRemU,
			OpAnd, OpOr, OpXor, OpShl, OpShr, OpShrU:
			b, err := pop(2)
			if err != nil {
				return nil, err
			}
			stack = append(stack, evalIntBinOp(instr.Op, b[0], b[1]))
		case OpNegI, OpNot:
			v, err := pop(1)
			if err != nil {
				return nil, err
			}
			stack = append(stack, evalIntUnOp(instr.Op, v[0]))

		case OpAddF, OpSubF, OpMulF, OpDivF, OpRemF:
			b, err := pop(2)
			if err != nil {
				return nil, err
			}
			stack = append(stack, evalFloatBinOp(instr.Op, b[0], b[1]))
		case OpNegF:
			v, err := pop(1)
			if err != nil {
				return nil, err
			}
			stack = append(stack, math.Float64bits(-math.Float64frombits(v[0])))

		case OpEqI, OpNeI, OpLtI, OpLeI, OpGtI, OpGeI,
			OpLtU, OpLeU, OpGtU, OpGeU:
			b, err := pop(2)
			if err != nil {
				return nil, err
			}
			stack = append(stack, evalIntCmp(instr.Op, b[0], b[1]))
		case OpEqF, OpNeF, OpLtF, OpLeF, OpGtF, OpGeF:
			b, err := pop(2)
			if err != nil {
				return nil, err
			}
			stack = append(stack, evalFloatCmp(instr.Op, b[0], b[1]))

		case OpNotB:
			v, err := pop(1)
			if err != nil {
				return nil, err
			}
			stack = append(stack, 1-v[0])
		case OpConvert:
			v, err := pop(1)
			if err != nil {
				return nil, err
			}
			stack = append(stack, Convert(v[0], instr.Arg))

		case OpJump:
			if instr.Arg%InstrSize != 0 || instr.Arg < 0 || int(instr.Arg) >= len(cur.Code) {
				return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: "branch target out of range"}
			}
			nextPC = int(instr.Arg)
		case OpJumpIfZero, OpJumpIfNotZero:
			v, err := pop(1)
			if err != nil {
				return nil, err
			}
			taken := (v[0] == 0) == (instr.Op == OpJumpIfZero)
			if taken {
				if instr.Arg%InstrSize != 0 || instr.Arg < 0 || int(instr.Arg) >= len(cur.Code) {
					return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: "branch target out of range"}
				}
				nextPC = int(instr.Arg)
			}

		case OpDispatch:
			v, err := pop(1)
			if err != nil {
				return nil, err
			}
			if len(cur.Dispatch) == 0 {
				return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: "dispatch with no dispatch table"}
			}
			if v[0] >= uint64(len(cur.Dispatch)) {
				return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: fmt.Sprintf("dispatch state %d out of range", v[0])}
			}
			target := int(cur.Dispatch[v[0]])
			if target%InstrSize != 0 || target < 0 || target >= len(cur.Code) {
				return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: "dispatch target out of range"}
			}
			nextPC = target

		case OpCallV:
			if instr.Arg < 0 || int(instr.Arg) >= len(p.Funcs) {
				return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: "virtual call target out of range"}
			}
			callee := p.Funcs[instr.Arg]
			if len(frames) >= maxCallDepth {
				return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: "virtual call stack overflow"}
			}
			argv, err := pop(len(callee.Params))
			if err != nil {
				return nil, err
			}
			newLocals := make([]uint64, callee.NumLocals)
			copy(newLocals, argv)
			frames = append(frames, frame{fn: cur, locals: locals, retPC: nextPC, retFn: -1})
			cur, locals, pc = callee, newLocals, 0
			continue

		case OpCallN:
			if instr.Arg < 0 || int(instr.Arg) >= len(p.Natives) {
				return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: "native call target out of range"}
			}
			native := p.Natives[instr.Arg]
			if p.nativeImpl == nil {
				return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: "native call with no native implementation bound"}
			}
			argv, err := pop(len(native.Params))
			if err != nil {
				return nil, err
			}
			results := p.nativeImpl(int(instr.Arg), argv)
			stack = append(stack, results...)

		case OpReturn:
			n := int(instr.Arg)
			if n < 0 || n > len(stack) {
				return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: "invalid return arity"}
			}
			results := append([]uint64(nil), stack[len(stack)-n:]...)
			stack = stack[:len(stack)-n]
			if len(frames) == 0 {
				return results, nil
			}
			f := frames[len(frames)-1]
			frames = frames[:len(frames)-1]
			cur, locals, pc = f.fn, f.locals, f.retPC
			stack = append(stack, results...)
			continue

		case OpNested:
			if instr.Arg < 0 || int(instr.Arg) >= len(p.Nested) {
				return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: "nested blob out of range"}
			}
			// Nested virtualization: run blob as a mini program with nested key.
			blob := p.Nested[instr.Arg]
			nk := p.Key
			if p.Hardening != nil {
				nk = p.Hardening.NestedKey
			}
			nestedProg := &Program{Key: nk, Hardening: p.Hardening, Funcs: []*Function{{
				Name: cur.Name + "/nested",
				Code: blob,
				Params: nil,
				Results: nil,
				NumLocals: 0,
			}}}
			// Execute nested with empty args; push results onto stack.
			out, err := nestedProg.RunFunc(0)
			if err != nil {
				return nil, err
			}
			stack = append(stack, out...)

		case OpHalt:
			return append([]uint64(nil), stack...), nil

		default:
			return nil, &ExecutionError{Func: cur.Name, PC: pc, Msg: fmt.Sprintf("unknown opcode %d", instr.Op)}
		}
		pc = nextPC
	}
}

// nativeImpl is bound by BindNatives so that the interpreter can call back into
// real Go functions during tests.
func (p *Program) nativeImplFor() func(int, []uint64) []uint64 { return p.nativeImpl }

// evalIntBinOp implements the integer binary operations. The expressions are
// written exactly as the emitted runtime writes them, so that the interpreter
// and the shipped program agree on overflow, shift and division semantics.
func evalIntBinOp(op Opcode, a, b uint64) uint64 {
	switch op {
	case OpAddI:
		return a + b
	case OpSubI:
		return a - b
	case OpMulI:
		return a * b
	case OpDivI:
		return uint64(int64(a) / int64(b))
	case OpRemI:
		return uint64(int64(a) % int64(b))
	case OpDivU:
		return a / b
	case OpRemU:
		return a % b
	case OpAnd:
		return a & b
	case OpOr:
		return a | b
	case OpXor:
		return a ^ b
	case OpShl:
		return a << (b & 63)
	case OpShr:
		return uint64(int64(a) >> (b & 63))
	case OpShrU:
		return a >> (b & 63)
	}
	panic("vm: not an integer binary operation: " + op.String())
}

func evalIntUnOp(op Opcode, a uint64) uint64 {
	switch op {
	case OpNegI:
		return -a
	case OpNot:
		return ^a
	}
	panic("vm: not an integer unary operation: " + op.String())
}

func evalFloatBinOp(op Opcode, a, b uint64) uint64 {
	x, y := math.Float64frombits(a), math.Float64frombits(b)
	switch op {
	case OpAddF:
		return math.Float64bits(x + y)
	case OpSubF:
		return math.Float64bits(x - y)
	case OpMulF:
		return math.Float64bits(x * y)
	case OpDivF:
		return math.Float64bits(x / y)
	case OpRemF:
		return math.Float64bits(math.Mod(x, y))
	}
	panic("vm: not a float binary operation: " + op.String())
}

func evalIntCmp(op Opcode, a, b uint64) uint64 {
	var res bool
	switch op {
	case OpEqI:
		res = a == b
	case OpNeI:
		res = a != b
	case OpLtI:
		res = int64(a) < int64(b)
	case OpLeI:
		res = int64(a) <= int64(b)
	case OpGtI:
		res = int64(a) > int64(b)
	case OpGeI:
		res = int64(a) >= int64(b)
	case OpLtU:
		res = a < b
	case OpLeU:
		res = a <= b
	case OpGtU:
		res = a > b
	case OpGeU:
		res = a >= b
	default:
		panic("vm: not an integer comparison: " + op.String())
	}
	if res {
		return 1
	}
	return 0
}

func evalFloatCmp(op Opcode, a, b uint64) uint64 {
	x, y := math.Float64frombits(a), math.Float64frombits(b)
	var res bool
	switch op {
	case OpEqF:
		res = x == y
	case OpNeF:
		res = x != y
	case OpLtF:
		res = x < y
	case OpLeF:
		res = x <= y
	case OpGtF:
		res = x > y
	case OpGeF:
		res = x >= y
	default:
		panic("vm: not a float comparison: " + op.String())
	}
	if res {
		return 1
	}
	return 0
}
