package vm

import (
	"bytes"
	"fmt"
	"go/types"
	"strings"
	"testing"

	"github.com/go-quicktest/qt"
)

// flattenSrc is a corpus of single-word functions covering straight-line code,
// branches, loops with phi nodes, recursion through OpCallV and float words.
const flattenSrc = `package p

func add(a, b int) int { return a + b }

func fib(n int) int {
	if n < 2 {
		return n
	}
	return fib(n-1) + fib(n-2)
}

func loop(n int) int {
	sum := 0
	for i := 0; i < n; i++ {
		if i%2 == 0 {
			sum += i
		}
	}
	return sum
}

func mixed(a, b int32, f float64, u uint8) (int32, float64) {
	return a*b + int32(u), f / 2
}

func boolLogic(a, b bool) bool { return a && !b }
`

// flattenProgram compiles flattenSrc into a verified program.
func flattenProgram(t *testing.T, key uint64) *Program {
	t.Helper()
	ssaPkg := buildSSAForTest(t, flattenSrc)
	comp := NewCompiler(key, func(*types.Package) string { return "" })

	// The order fixes the function indices used by the callers below.
	names := []string{"add", "fib", "loop", "mixed", "boolLogic"}
	for _, name := range names {
		comp.Add(ssaPkg.Func(name))
	}
	for _, name := range names {
		_, err := comp.Compile(ssaPkg.Func(name))
		qt.Assert(t, qt.IsNil(err), qt.Commentf("compiling %s", name))
	}
	return comp.Program()
}

// flattenCalls are representative invocations of every function in
// flattenProgram, chosen so that before-and-after runs must agree exactly.
var flattenCalls = []struct {
	fn   int
	args []uint64
}{
	{0, []uint64{wordOfInt(1), wordOfInt(2)}},
	{0, []uint64{wordOfInt(-5), wordOfInt(5)}},
	{1, []uint64{wordOfInt(0)}},
	{1, []uint64{wordOfInt(10)}},
	{2, []uint64{wordOfInt(0)}},
	{2, []uint64{wordOfInt(100)}},
	{3, []uint64{wordOfInt(3), wordOfInt(4), floatBits(9.0), 7}},
	{4, []uint64{1, 0}},
	{4, []uint64{0, 0}},
	{4, []uint64{1, 1}},
}

// runCalls executes the corpus and renders every result, which makes a
// before-and-after comparison a single string equality.
func runCalls(t *testing.T, p *Program) string {
	t.Helper()
	var sb strings.Builder
	for _, c := range flattenCalls {
		got, err := p.RunFunc(c.fn, c.args...)
		qt.Assert(t, qt.IsNil(err), qt.Commentf("calling function %d", c.fn))
		fmt.Fprintf(&sb, "f%d(%v) = %v\n", c.fn, c.args, got)
	}
	return sb.String()
}

func decodeAll(p *Program, f *Function) []Instruction {
	instrs := make([]Instruction, f.NumInstrs())
	for i := range instrs {
		instrs[i] = DecodeHard(f.Code, i*InstrSize, p.Key, p.Hardening)
	}
	return instrs
}

// assertFlattened checks the structural shape of a flattened program: the
// entry is a dispatch prologue, direct branches are gone, every table target is
// an instruction boundary and every conditional lands on a dispatch stub.
func assertFlattened(t *testing.T, p *Program) {
	t.Helper()
	for i, f := range p.Funcs {
		qt.Assert(t, qt.IsTrue(len(f.Dispatch) > 0), qt.Commentf("function %d has no dispatch table", i))
		instrs := decodeAll(p, f)

		// The entry point must be a prologue that dispatches to the original
		// entry block, because a virtual call starts at offset zero.
		qt.Assert(t, qt.Equals(instrs[0].Op, OpConst), qt.Commentf("function %d: entry is not a Const", i))
		qt.Assert(t, qt.Equals(instrs[1].Op, OpDispatch), qt.Commentf("function %d: entry is not a Dispatch", i))

		for pc, instr := range instrs {
			switch instr.Op {
			case OpJump:
				t.Errorf("function %d still contains a direct jump at %04d", i, pc*InstrSize)
			case OpJumpIfZero, OpJumpIfNotZero:
				// The only remaining conditional branch is the stub selector.
				// Its target must be a dispatch stub.
				idx := int(instr.Arg) / InstrSize
				if idx < 0 || idx+1 >= len(instrs) {
					t.Fatalf("function %d: conditional target %d is out of range", i, instr.Arg)
				}
				if instrs[idx].Op != OpConst || instrs[idx+1].Op != OpDispatch {
					t.Errorf("function %d: conditional at %04d does not target a dispatch stub", i, pc*InstrSize)
				}
				// Its fallthrough must reach a dispatch too, possibly after a
				// decoy predicate.
				found := false
				for j := pc + 1; j+1 < len(instrs) && j <= pc+decoyPredicateLen+2; j++ {
					if instrs[j].Op == OpConst && instrs[j+1].Op == OpDispatch {
						found = true
						break
					}
				}
				if !found {
					t.Errorf("function %d: conditional at %04d has no dispatch on its fallthrough path", i, pc*InstrSize)
				}
			}
		}

		for _, target := range f.Dispatch {
			qt.Assert(t, qt.IsTrue(int(target) >= 0 && int(target) < len(f.Code) && int(target)%InstrSize == 0),
				qt.Commentf("function %d: dispatch target %d is not an instruction boundary", i, target))
		}
	}
}

func TestFlattenPreservesSemantics(t *testing.T) {
	// The seed only chooses the permutations, so every seed must preserve the
	// program's meaning.
	for _, seed := range []uint64{1, 0x1234, 0xdeadbeef, 0xffffffffffffffff} {
		prog := flattenProgram(t, 0xabcdef)
		want := runCalls(t, prog)

		qt.Assert(t, qt.IsNil(prog.Flatten(DefaultFlattenOptions(seed))), qt.Commentf("seed %#x", seed))
		qt.Assert(t, qt.IsNil(prog.CheckAll()), qt.Commentf("seed %#x", seed))
		qt.Assert(t, qt.Equals(runCalls(t, prog), want), qt.Commentf("seed %#x", seed))
		assertFlattened(t, prog)
	}
}

func TestFlattenWithDecoysPreservesSemantics(t *testing.T) {
	prog := flattenProgram(t, 0xabcdef)
	want := runCalls(t, prog)

	opts := DefaultFlattenOptions(0x5eed)
	opts.DecoyEdges = true
	qt.Assert(t, qt.IsNil(prog.Flatten(opts)))
	qt.Assert(t, qt.IsNil(prog.CheckAll()))
	qt.Assert(t, qt.Equals(runCalls(t, prog), want))
	assertFlattened(t, prog)
}

func TestFlattenIsDeterministic(t *testing.T) {
	opts := DefaultFlattenOptions(42)

	first := flattenProgram(t, 0xabcdef)
	second := flattenProgram(t, 0xabcdef)
	qt.Assert(t, qt.IsNil(first.Flatten(opts)))
	qt.Assert(t, qt.IsNil(second.Flatten(opts)))

	for i := range first.Funcs {
		qt.Assert(t, qt.DeepEquals(first.Funcs[i].Code, second.Funcs[i].Code), qt.Commentf("function %d code", i))
		qt.Assert(t, qt.DeepEquals(first.Funcs[i].Dispatch, second.Funcs[i].Dispatch), qt.Commentf("function %d table", i))
	}
}

// TestFlattenVariesWithSeed checks that the permutations actually depend on the
// seed; an obfuscation that produces the same layout every build would be
// pointless.
func TestFlattenVariesWithSeed(t *testing.T) {
	first := flattenProgram(t, 0xabcdef)
	second := flattenProgram(t, 0xabcdef)
	qt.Assert(t, qt.IsNil(first.Flatten(DefaultFlattenOptions(1))))
	qt.Assert(t, qt.IsNil(second.Flatten(DefaultFlattenOptions(2))))

	differs := false
	for i := range first.Funcs {
		if !bytes.Equal(first.Funcs[i].Code, second.Funcs[i].Code) {
			differs = true
		}
	}
	qt.Assert(t, qt.IsTrue(differs), qt.Commentf("two seeds produced identical bytecode"))
}

// TestFlattenDecoratesTheDispatchTable checks that table padding and the decoy
// edges add material an analyst has to resolve.
func TestFlattenDecoratesTheDispatchTable(t *testing.T) {
	plain := flattenProgram(t, 0xabcdef)
	decorated := flattenProgram(t, 0xabcdef)

	plainOpts := FlattenOptions{Seed: 3}
	decoratedOpts := FlattenOptions{Seed: 3, TablePadding: 6, DecoyEdges: true}
	qt.Assert(t, qt.IsNil(plain.Flatten(plainOpts)))
	qt.Assert(t, qt.IsNil(decorated.Flatten(decoratedOpts)))

	var plainBytes, decoratedBytes int
	for i := range plain.Funcs {
		qt.Assert(t, qt.Equals(len(decorated.Funcs[i].Dispatch), len(plain.Funcs[i].Dispatch)+6),
			qt.Commentf("function %d table padding", i))
		plainBytes += len(plain.Funcs[i].Code)
		decoratedBytes += len(decorated.Funcs[i].Code)
	}
	// Decoys are only added to blocks that transfer control, so a function that
	// is a single straight-line block is unchanged. The program as a whole must
	// still grow, since the corpus has branches.
	qt.Assert(t, qt.IsTrue(decoratedBytes > plainBytes), qt.Commentf("decoys did not grow the program"))
	qt.Assert(t, qt.IsNil(decorated.CheckAll()))
}

func TestFlattenFlattensOnlyOnce(t *testing.T) {
	prog := flattenProgram(t, 0xabcdef)
	qt.Assert(t, qt.IsNil(prog.Flatten(DefaultFlattenOptions(1))))

	savedCode := make([][]byte, len(prog.Funcs))
	for i, f := range prog.Funcs {
		savedCode[i] = append([]byte(nil), f.Code...)
	}

	err := prog.Flatten(DefaultFlattenOptions(1))
	qt.Assert(t, qt.IsNotNil(err))
	qt.Assert(t, qt.StringContains(err.Error(), "already flattened"))

	// The failed call must have left the program exactly as it was.
	for i, f := range prog.Funcs {
		qt.Assert(t, qt.DeepEquals(f.Code, savedCode[i]), qt.Commentf("function %d changed", i))
	}
	qt.Assert(t, qt.IsNil(prog.CheckAll()))
}

// TestFlattenFailureIsAtomic checks that a failure in a later function rolls
// back the functions that were already rewritten.
func TestFlattenFailureIsAtomic(t *testing.T) {
	ssaPkg := buildSSAForTest(t, flattenSrc)
	comp := NewCompiler(0xabcdef, func(*types.Package) string { return "" })
	comp.Add(ssaPkg.Func("add"))
	_, err := comp.Compile(ssaPkg.Func("add"))
	qt.Assert(t, qt.IsNil(err))

	// A second function whose body has an instruction after an unconditional
	// jump cannot be split into blocks, so flattening must fail on it.
	broken := NewBuilder()
	broken.Emit(OpJump, 3*InstrSize)
	broken.Emit(OpConst, 1)
	broken.Emit(OpPop, 0)
	broken.Emit(OpConst, 0)
	broken.Emit(OpReturn, 1)
	brokenFunc := &Function{
		Name:       "broken",
		Results:    []ValType{TypeInt},
		NumLocals:  0,
		LocalTypes: []ValType{},
		Code:       broken.Encode(0xabcdef),
	}
	prog := comp.Program()
	prog.Funcs = append(prog.Funcs, brokenFunc)

	before := make([][]byte, len(prog.Funcs))
	for i, f := range prog.Funcs {
		before[i] = append([]byte(nil), f.Code...)
	}

	err = prog.Flatten(DefaultFlattenOptions(1))
	qt.Assert(t, qt.IsNotNil(err))
	qt.Assert(t, qt.StringContains(err.Error(), "broken"))

	for i, f := range prog.Funcs {
		qt.Assert(t, qt.DeepEquals(f.Code, before[i]), qt.Commentf("function %d changed", i))
		qt.Assert(t, qt.IsTrue(len(f.Dispatch) == 0), qt.Commentf("function %d gained a table", i))
	}
}

// TestVerifyDispatchRejections covers the ways a dispatch can be malformed.
func TestVerifyDispatchRejections(t *testing.T) {
	build := func(dispatch []int32, code *Builder, locals []ValType) *Program {
		p := singleFunc(code, len(locals), nil, []ValType{TypeInt})
		p.Funcs[0].NumLocals = len(locals)
		p.Funcs[0].LocalTypes = locals
		p.Funcs[0].Dispatch = dispatch
		return p
	}

	// No dispatch table at all.
	b := NewBuilder()
	b.Emit(OpConst, 0)
	b.Emit(OpDispatch, 0)
	b.Emit(OpConst, 0)
	b.Emit(OpReturn, 1)
	err := build(nil, b, nil).Verify()
	qt.Assert(t, qt.IsNotNil(err))
	qt.Assert(t, qt.StringContains(err.Error(), "dispatch table"))

	// A target that is not an instruction boundary.
	b = NewBuilder()
	b.Emit(OpConst, 0)
	b.Emit(OpDispatch, 0)
	b.Emit(OpConst, 0)
	b.Emit(OpReturn, 1)
	err = build([]int32{1}, b, nil).Verify()
	qt.Assert(t, qt.IsNotNil(err))
	qt.Assert(t, qt.StringContains(err.Error(), "instruction boundary"))

	// A target past the end of the code.
	err = build([]int32{int32(b.Len())}, b, nil).Verify()
	qt.Assert(t, qt.IsNotNil(err))
	qt.Assert(t, qt.StringContains(err.Error(), "instruction boundary"))

	// A state word that is not an integer.
	b = NewBuilder()
	b.Emit(OpConstF, 0)
	b.Emit(OpDispatch, 0)
	b.Emit(OpConst, 0)
	b.Emit(OpReturn, 1)
	err = build([]int32{0}, b, nil).Verify()
	qt.Assert(t, qt.IsNotNil(err))
	qt.Assert(t, qt.StringContains(err.Error(), "want int"))

	// A dispatch on an empty stack.
	b = NewBuilder()
	b.Emit(OpDispatch, 0)
	b.Emit(OpConst, 0)
	b.Emit(OpReturn, 1)
	err = build([]int32{0}, b, nil).Verify()
	qt.Assert(t, qt.IsNotNil(err))
	qt.Assert(t, qt.StringContains(err.Error(), "requires 1 operand"))

	// A well-formed dispatch is accepted: push state 0, dispatch through the
	// table to the instruction that produces the result.
	b = NewBuilder()
	b.Emit(OpConst, 0)
	b.Emit(OpDispatch, 0)
	b.Emit(OpConst, 7)
	b.Emit(OpReturn, 1)
	prog := build([]int32{2 * InstrSize}, b, nil)
	qt.Assert(t, qt.IsNil(prog.Verify()))
	got, err := prog.Run()
	qt.Assert(t, qt.IsNil(err))
	qt.Assert(t, qt.DeepEquals(got, []uint64{wordOfInt(7)}))
}

// TestFlattenedRuntimeMatchesInterpreter is the end-to-end guarantee: the
// generated Go dispatch loop must execute flattened bytecode exactly like the
// reference interpreter, including the new indirect branch.
func TestFlattenedRuntimeMatchesInterpreter(t *testing.T) {
	prog := flattenProgram(t, 0xabcdef)
	qt.Assert(t, qt.IsNil(prog.Flatten(DefaultFlattenOptions(0x5eed))))

	// Every call below returns a single word, so each line of the program's
	// output corresponds to one interpreter result.
	calls := []struct {
		fn   int
		args []uint64
	}{
		{0, []uint64{wordOfInt(1), wordOfInt(2)}},
		{0, []uint64{wordOfInt(-5), wordOfInt(5)}},
		{1, []uint64{wordOfInt(10)}},
		{2, []uint64{wordOfInt(100)}},
		{4, []uint64{1, 0}},
	}

	var want, body strings.Builder
	for i, c := range calls {
		got, err := prog.RunFunc(c.fn, c.args...)
		qt.Assert(t, qt.IsNil(err))
		fmt.Fprintf(&want, "%d\n", got[0])

		args := make([]string, len(c.args))
		for j, a := range c.args {
			args[j] = fmt.Sprint(a)
		}
		fmt.Fprintf(&body, "\tr%d := _vmp_Run(%d, []uint64{%s})\n", i, c.fn, strings.Join(args, ", "))
		fmt.Fprintf(&body, "\tfmt.Println(r%d[0])\n", i)
	}

	out := runEmitted(t, prog, body.String())
	qt.Assert(t, qt.DeepEquals(strings.Fields(out), strings.Fields(want.String())))
}

// BenchmarkInterpreterLoopFlattened measures the cost of the indirect dispatch
// on the hot path, relative to BenchmarkInterpreterLoop.
func BenchmarkInterpreterLoopFlattened(b *testing.B) {
	p := loopProgram()
	if err := p.Flatten(DefaultFlattenOptions(p.Key)); err != nil {
		b.Fatal(err)
	}
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

// BenchmarkInterpreterLoopFlattenedDecoys measures the extra cost of the
// opaque-predicate decoy edges.
func BenchmarkInterpreterLoopFlattenedDecoys(b *testing.B) {
	p := loopProgram()
	opts := DefaultFlattenOptions(p.Key)
	opts.DecoyEdges = true
	if err := p.Flatten(opts); err != nil {
		b.Fatal(err)
	}
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
