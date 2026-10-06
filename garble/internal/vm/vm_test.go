package vm

import (
	"math"
	"strings"
	"testing"

	"github.com/go-quicktest/qt"
)

func TestEncodeDecodeRoundTrip(t *testing.T) {
	key := uint64(0xdeadbeefcafef00d)
	instrs := []Instruction{
		{Op: OpConst, Arg: 42},
		{Op: OpLoadLocal, Arg: -1},
		{Op: OpJump, Arg: 12345},
		{Op: OpReturn, Arg: 3},
		{Op: OpConvert, Arg: MakeConvertOperand(KindF64, 64, KindInt, 32)},
	}
	for _, want := range instrs {
		encoded := Encode(want.Op, want.Arg, key)
		qt.Assert(t, qt.Equals(len(encoded), InstrSize))
		got := DecodeInstruction(encoded, 0, key)
		qt.Assert(t, qt.Equals(got.Op, want.Op))
		qt.Assert(t, qt.Equals(got.Arg, want.Arg))
	}
}

// TestEncodingIsObfuscated checks that the encoded stream does not literally
// contain the plaintext opcode bytes, which is the whole point of the key.
func TestEncodingIsObfuscated(t *testing.T) {
	key := uint64(0x0123456789abcdef)
	encoded := Encode(OpReturn, 7, key)
	qt.Assert(t, qt.Not(qt.Equals(encoded[0], byte(OpReturn))))
	// With a zero key the encoding is the documented, readable one.
	plain := Encode(OpReturn, 7, 0)
	qt.Assert(t, qt.Equals(plain[0], byte(OpReturn)))
}

func TestBuilderPatch(t *testing.T) {
	b := NewBuilder()
	b.Emit(OpNop, 0)
	pc := b.Emit(OpJump, 0)
	qt.Assert(t, qt.Equals(b.Len(), 2*InstrSize))
	b.Patch(pc, int64(b.Len()))
	encoded := b.Encode(0)
	got := DecodeInstruction(encoded, pc, 0)
	qt.Assert(t, qt.Equals(got.Op, OpJump))
	qt.Assert(t, qt.Equals(got.Arg, int64(2*InstrSize)))
}

func TestBuilderPatchRejectsBadOffset(t *testing.T) {
	b := NewBuilder()
	b.Emit(OpNop, 0)
	mustPanic(t, func() { b.Patch(1, 0) })
	mustPanic(t, func() { b.Patch(4*InstrSize, 0) })
}

func TestDisassemble(t *testing.T) {
	b := NewBuilder()
	b.Emit(OpConst, 5)
	b.Emit(OpReturn, 1)
	out := Disassemble(b.Encode(0), 0)
	qt.Assert(t, qt.StringContains(out, "CONST"))
	qt.Assert(t, qt.StringContains(out, "RET"))
	qt.Assert(t, qt.StringContains(out, "0000"))
	qt.Assert(t, qt.StringContains(out, "0009"))
}

func TestOpcodeDocsCoverInstructionSet(t *testing.T) {
	// Every opcode must have both a mnemonic and reference documentation; the
	// docs are the contract for the instruction set.
	for op := Opcode(0); op < opCount; op++ {
		qt.Assert(t, qt.IsTrue(opNames[op] != ""), qt.Commentf("opcode %d has no mnemonic", op))
		qt.Assert(t, qt.IsTrue(opDocs[op] != ""), qt.Commentf("opcode %d (%s) has no docs", op, op))
	}
	// Every instruction with a fixed effect must also have a dispatcher body,
	// otherwise the emitted runtime would panic on it.
	for op := Opcode(0); op < opCount; op++ {
		if _, ok := opEffects[op]; ok {
			_, hasBody := opBodies[op]
			qt.Assert(t, qt.IsTrue(hasBody), qt.Commentf("opcode %d (%s) has no emitted body", op, op))
		}
	}
}

func TestConvertSemantics(t *testing.T) {
	// int64 -> int32 truncates.
	got := Convert(wordOfInt(-1), MakeConvertOperand(KindInt, 64, KindInt, 32))
	qt.Assert(t, qt.Equals(int64(got), int64(-1)))

	// 0x1_0000_0001 -> int32 is 1.
	got = Convert(0x100000001, MakeConvertOperand(KindInt, 64, KindInt, 32))
	qt.Assert(t, qt.Equals(int64(got), int64(1)))

	// int -> uint8 wraps.
	got = Convert(wordOfInt(-1), MakeConvertOperand(KindInt, 64, KindUint, 8))
	qt.Assert(t, qt.Equals(got, uint64(255)))

	// int -> float64.
	got = Convert(wordOfInt(7), MakeConvertOperand(KindInt, 64, KindF64, 64))
	qt.Assert(t, qt.Equals(math.Float64frombits(got), float64(7)))

	// float64 -> int64 truncates toward zero.
	got = Convert(math.Float64bits(-2.9), MakeConvertOperand(KindF64, 64, KindInt, 64))
	qt.Assert(t, qt.Equals(int64(got), int64(-2)))

	// float64 -> float32 rounds.
	got = Convert(math.Float64bits(1.1), MakeConvertOperand(KindF64, 64, KindF32, 32))
	qt.Assert(t, qt.Equals(math.Float32frombits(uint32(got)), float32(1.1)))
}

func TestConvertOperandRoundTrip(t *testing.T) {
	op := MakeConvertOperand(KindUint, 32, KindF32, 32)
	fk, fb, tk, tb := UnpackConvertOperand(op)
	qt.Assert(t, qt.Equals(fk, KindUint))
	qt.Assert(t, qt.Equals(fb, 32))
	qt.Assert(t, qt.Equals(tk, KindF32))
	qt.Assert(t, qt.Equals(tb, 32))
}

// verifierProgram builds a program from a builder with the given frame layout.
func verifierProgram(b *Builder, numLocals int, localTypes []ValType, params, results []ValType) *Program {
	key := uint64(0xabcd)
	return &Program{
		Key: key,
		Funcs: []*Function{{
			Name:       "f",
			Params:     params,
			Results:    results,
			NumLocals:  numLocals,
			LocalTypes: localTypes,
			Code:       b.Encode(key),
		}},
	}
}

func TestVerifyRejects(t *testing.T) {
	anyLocals := func(n int) []ValType {
		out := make([]ValType, n)
		for i := range out {
			out[i] = TypeAny
		}
		return out
	}

	cases := []struct {
		name    string
		build   func() *Program
		wantSub string
	}{
		{"empty", func() *Program {
			return verifierProgram(NewBuilder(), 0, nil, nil, nil)
		}, "empty code"},
		{"stack underflow", func() *Program {
			b := NewBuilder()
			b.Emit(OpAddI, 0)
			b.Emit(OpReturn, 0)
			return verifierProgram(b, 0, nil, nil, nil)
		}, "requires 2 operand"},
		{"branch target not aligned", func() *Program {
			b := NewBuilder()
			b.Emit(OpJump, 1)
			return verifierProgram(b, 0, nil, nil, nil)
		}, "not a valid instruction boundary"},
		{"branch target out of range", func() *Program {
			b := NewBuilder()
			b.Emit(OpJump, int64(10*InstrSize))
			return verifierProgram(b, 0, nil, nil, nil)
		}, "not a valid instruction boundary"},
		{"local out of range", func() *Program {
			b := NewBuilder()
			b.Emit(OpLoadLocal, 5)
			b.Emit(OpReturn, 1)
			return verifierProgram(b, 1, anyLocals(1), nil, []ValType{TypeInt})
		}, "out of range"},
		{"return arity mismatch", func() *Program {
			b := NewBuilder()
			b.Emit(OpConst, 1)
			b.Emit(OpConst, 2)
			b.Emit(OpReturn, 2)
			// The function declares a single result, so returning two is invalid
			// even though two values are on the stack.
			return verifierProgram(b, 0, nil, nil, []ValType{TypeInt})
		}, "return of 2 value(s), function declares 1"},
		{"unreachable instruction", func() *Program {
			b := NewBuilder()
			b.Emit(OpReturn, 0)
			b.Emit(OpNop, 0)
			return verifierProgram(b, 0, nil, nil, nil)
		}, "unreachable instruction"},
		{"control falls off the end", func() *Program {
			b := NewBuilder()
			b.Emit(OpNop, 0)
			b.Emit(OpNop, 0)
			return verifierProgram(b, 0, nil, nil, nil)
		}, "falls off the end"},
		{"type mismatch", func() *Program {
			// Load a float local, then use it as an integer operand.
			b := NewBuilder()
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpConst, 1)
			b.Emit(OpAddI, 0)
			b.Emit(OpPop, 0)
			b.Emit(OpReturn, 0)
			return verifierProgram(b, 1, []ValType{TypeFloat}, []ValType{TypeFloat}, nil)
		}, "want int"},
		{"merge stack depth mismatch", func() *Program {
			// One branch reaches the target with depth 0 and the other with depth
			// 1, so the join has no single meaning.
			b := NewBuilder()
			b.Emit(OpLoadLocal, 0)                   // depth 1
			b.Emit(OpJumpIfZero, int64(5*InstrSize)) // pops -> depth 0, target below
			b.Emit(OpJump, int64(4*InstrSize))       // depth 0, jumps to the join
			b.Emit(OpNop, 0)                         // join point, reached at depth 0
			b.Emit(OpConst, 9)                       // depth 1, falls through to join
			b.Emit(OpNop, 0)                         // the other join point
			b.Emit(OpReturn, 0)
			return verifierProgram(b, 1, []ValType{TypeInt}, nil, nil)
		}, "incompatible stack depths"},
		{"call to missing virtual function", func() *Program {
			b := NewBuilder()
			b.Emit(OpCallV, 9)
			b.Emit(OpReturn, 0)
			return verifierProgram(b, 0, nil, nil, nil)
		}, "out of range"},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			err := tc.build().Verify()
			qt.Assert(t, qt.IsNotNil(err))
			qt.Assert(t, qt.StringContains(err.Error(), tc.wantSub))
		})
	}
}

func TestVerifyAcceptsWellFormedProgram(t *testing.T) {
	b := NewBuilder()
	b.Emit(OpLoadLocal, 0)
	b.Emit(OpLoadLocal, 1)
	b.Emit(OpAddI, 0)
	b.Emit(OpReturn, 1)
	p := verifierProgram(b, 2, []ValType{TypeInt, TypeInt}, []ValType{TypeInt, TypeInt}, []ValType{TypeInt})
	qt.Assert(t, qt.IsNil(p.Verify()))
	qt.Assert(t, qt.Equals(p.Funcs[0].MaxStack, 2))
}

// TestVerifyRejectsInfiniteLoopOnlyIfUnreachableTail guards the reachability
// rule: a backward jump is fine, but an instruction that nothing can reach is
// rejected because its stack effect can never be checked.
func TestVerifyRejectsInfiniteLoopOnlyIfUnreachableTail(t *testing.T) {
	b := NewBuilder()
	loop := b.Emit(OpNop, 0)
	b.Emit(OpJump, int64(loop))
	qt.Assert(t, qt.IsNil(verifierProgram(b, 0, nil, nil, nil).Verify()))
}

func TestRunDivByZeroPanics(t *testing.T) {
	b := NewBuilder()
	b.Emit(OpLoadLocal, 0)
	b.Emit(OpLoadLocal, 1)
	b.Emit(OpDivI, 0)
	b.Emit(OpReturn, 1)
	p := singleFunc(b, 2, []ValType{TypeInt, TypeInt}, []ValType{TypeInt})
	qt.Assert(t, qt.IsNil(p.Verify()))
	mustPanic(t, func() { p.Run(1, 0) })
}

// mustPanic fails the test unless f panics.
func mustPanic(t *testing.T, f func()) {
	t.Helper()
	defer func() {
		if recover() == nil {
			t.Fatal("expected panic, got none")
		}
	}()
	f()
}

func TestRunNativeCall(t *testing.T) {
	b := NewBuilder()
	b.Emit(OpLoadLocal, 0)
	b.Emit(OpCallN, 0)
	b.Emit(OpReturn, 1)
	p := &Program{
		Key:        1,
		Natives:    []*NativeFunc{{GoName: "inc", Params: []ValType{TypeInt}, Results: []ValType{TypeInt}}},
		Funcs:      []*Function{{Name: "f", Params: []ValType{TypeInt}, Results: []ValType{TypeInt}, NumLocals: 1, LocalTypes: []ValType{TypeInt}}},
		nativeImpl: func(index int, args []uint64) []uint64 { return []uint64{args[0] + 1} },
	}
	p.Funcs[0].Code = b.Encode(p.Key)
	qt.Assert(t, qt.IsNil(p.Verify()))
	got, err := p.Run(41)
	qt.Assert(t, qt.IsNil(err))
	qt.Assert(t, qt.DeepEquals(got, []uint64{42}))
}

func TestInterpreterArityErrors(t *testing.T) {
	b := NewBuilder()
	b.Emit(OpLoadLocal, 0)
	b.Emit(OpReturn, 1)
	p := singleFunc(b, 1, []ValType{TypeInt}, []ValType{TypeInt})
	_, err := p.Run()
	qt.Assert(t, qt.IsNotNil(err))
	qt.Assert(t, qt.StringContains(err.Error(), "expects 1 argument"))

	_, err = p.RunFunc(5, 1)
	qt.Assert(t, qt.IsNotNil(err))
	qt.Assert(t, qt.StringContains(err.Error(), "out of range"))
}

func TestEmitRejectsUnverifiedProgram(t *testing.T) {
	b := NewBuilder()
	b.Emit(OpAddI, 0) // underflow
	b.Emit(OpReturn, 0)
	p := singleFunc(b, 0, nil, nil)
	opts := DefaultEmitterOptions()
	opts.PackageName = "main"
	_, err := p.Emit(opts)
	qt.Assert(t, qt.IsNotNil(err))
	qt.Assert(t, qt.StringContains(err.Error(), "verify"))
}

func TestEmitRejectsEmptyPrefix(t *testing.T) {
	b := NewBuilder()
	b.Emit(OpReturn, 0)
	p := singleFunc(b, 0, nil, nil)
	_, err := p.Emit(EmitterOptions{PackageName: "main"})
	qt.Assert(t, qt.IsNotNil(err))
	qt.Assert(t, qt.StringContains(err.Error(), "prefix"))
}

func TestDocAndString(t *testing.T) {
	qt.Assert(t, qt.Equals(OpAddI.String(), "ADD"))
	qt.Assert(t, qt.Equals(Opcode(250).String(), "OP?250"))
	qt.Assert(t, qt.StringContains(OpAddI.Doc(), "stack"))
	qt.Assert(t, qt.Equals(Opcode(250).Doc(), "unknown instruction"))
	qt.Assert(t, qt.Equals(TypeFloat.String(), "float"))
}

func TestNativeArityAndEffect(t *testing.T) {
	n := &NativeFunc{Params: []ValType{TypeInt, TypeFloat}}
	qt.Assert(t, qt.Equals(n.Arity(), 2))
	eff, ok := OpAddI.Effect()
	qt.Assert(t, qt.IsTrue(ok))
	qt.Assert(t, qt.Equals(eff.pop, 2))
	qt.Assert(t, qt.Equals(eff.push, 1))
	_, ok = OpCallV.Effect()
	qt.Assert(t, qt.IsFalse(ok))
}

// TestProgramDisassembleIsReadable is a smoke test for the tooling surface.
func TestProgramDisassembleIsReadable(t *testing.T) {
	b := NewBuilder()
	b.Emit(OpConst, 1)
	b.Emit(OpReturn, 1)
	p := singleFunc(b, 0, nil, []ValType{TypeInt})
	out := p.Disassemble()
	qt.Assert(t, qt.StringContains(out, "CONST"))
	qt.Assert(t, qt.StringContains(out, "locals="))
	qt.Assert(t, qt.IsTrue(strings.Count(out, "\n") > 2))
}
