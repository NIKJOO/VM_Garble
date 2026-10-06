package vm

import "testing"

// loopProgram builds a program equivalent to:
//
//	func loop(n int) int { sum := 0; for i := 0; i < n; i++ { sum += i }; return sum }
//
// It is the smallest program that exercises arithmetic, branches and phi
// assignments, so it is a fair stand-in for the hot path of the interpreter.
func loopProgram() *Program {
	b := NewBuilder()
	b.Emit(OpConst, 0)
	b.Emit(OpStoreLocal, 1) // sum = 0
	b.Emit(OpConst, 0)
	b.Emit(OpStoreLocal, 2) // i = 0
	loop := b.Len()
	b.Emit(OpLoadLocal, 2)
	b.Emit(OpLoadLocal, 0)
	b.Emit(OpLtI, 0)
	b.Emit(OpJumpIfZero, 0) // patched below
	exitJump := len(b.Instructions()) - 1
	b.Emit(OpLoadLocal, 1)
	b.Emit(OpLoadLocal, 2)
	b.Emit(OpAddI, 0)
	b.Emit(OpStoreLocal, 1)
	b.Emit(OpLoadLocal, 2)
	b.Emit(OpConst, 1)
	b.Emit(OpAddI, 0)
	b.Emit(OpStoreLocal, 2)
	b.Emit(OpJump, int64(loop))
	done := b.Len()
	b.Emit(OpLoadLocal, 1)
	b.Emit(OpReturn, 1)
	b.Patch(exitJump*InstrSize, int64(done))

	p := singleFunc(b, 3, []ValType{TypeInt}, []ValType{TypeInt})
	return p
}

func BenchmarkInterpreterLoop(b *testing.B) {
	p := loopProgram()
	if err := p.CheckAll(); err != nil {
		b.Fatal(err)
	}
	if _, err := p.RunFunc(0, 1000); err != nil {
		b.Fatal(err)
	}
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		if _, err := p.RunFunc(0, 1000); err != nil {
			b.Fatal(err)
		}
	}
}

func BenchmarkVerify(b *testing.B) {
	p := loopProgram()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		if err := p.CheckAll(); err != nil {
			b.Fatal(err)
		}
	}
}
