package vm

import (
	"errors"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"strings"
	"testing"

	"github.com/go-quicktest/qt"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
)

// buildSSAForTest type checks src as a single-file package and builds SSA for
// it. It is the bridge between Go source and the vm.Compiler under test.
func buildSSAForTest(t *testing.T, src string) *ssa.Package {
	t.Helper()
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "p.go", src, 0)
	qt.Assert(t, qt.IsNil(err))

	conf := &types.Config{Importer: importer.Default()}
	ssaPkg, _, err := ssautil.BuildPackage(conf, fset, types.NewPackage("p", "p"), []*ast.File{file}, ssa.InstantiateGenerics)
	qt.Assert(t, qt.IsNil(err))
	return ssaPkg
}

const eligibilitySrc = `package p

type iface interface{ Foo() int }

func nativeMul(a, b int) int { return a * b }

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
		sum += i
	}
	return sum
}

func callsNative(a, b int) int { return nativeMul(a, b) }

func mixed(a, b int32, f float64, u uint8) (int32, float64) {
	return a*b + int32(u), f / 2
}

func boolLogic(a, b bool) bool { return a && !b }

// The following are all outside the supported subset.

func closure() func() int { return func() int { return 1 } }

func variadic(xs ...int) int { return len(xs) }

func ifaceCall(i iface) int { return i.Foo() }

func heapAlloc() int {
	p := new(int)
	*p = 1
	return *p
}

func stringArg(s string) int { return len(s) }

func f32Arith(x, y float32) float32 { return x + y }

func useBuiltin(xs []int) int { return len(xs) }
`

func TestEligibility(t *testing.T) {
	ssaPkg := buildSSAForTest(t, eligibilitySrc)
	comp := NewCompiler(0x1234, func(*types.Package) string { return "" })

	supported := []string{"add", "fib", "loop", "callsNative", "mixed", "boolLogic", "f32Arith"}
	for _, name := range supported {
		fn := ssaPkg.Func(name)
		qt.Assert(t, qt.IsNotNil(fn), qt.Commentf("function %s not found", name))
		qt.Assert(t, qt.IsNil(comp.Eligible(fn)), qt.Commentf("expected %s to be eligible", name))
	}

	unsupported := map[string]string{
		"closure":    "closure",
		"variadic":   "variadic",
		"ifaceCall":  "unsupported type",
		"heapAlloc":  "heap",
		"stringArg":  "type",
		"useBuiltin": "builtin",
	}
	for name, wantReason := range unsupported {
		fn := ssaPkg.Func(name)
		qt.Assert(t, qt.IsNotNil(fn), qt.Commentf("function %s not found", name))
		err := comp.Eligible(fn)
		qt.Assert(t, qt.IsNotNil(err), qt.Commentf("expected %s to be rejected", name))

		var un *UnsupportedError
		qt.Assert(t, qt.IsTrue(errors.As(err, &un)), qt.Commentf("error for %s should be *UnsupportedError", name))
		qt.Assert(t, qt.StringContains(strings.ToLower(err.Error()), wantReason),
			qt.Commentf("error for %s should mention %q, got %q", name, wantReason, err))
	}
}

// TestRejectionsDoNotMutateState checks that a rejected function leaves the
// program unchanged, which is what makes safe fallback possible.
func TestRejectionsDoNotMutateState(t *testing.T) {
	ssaPkg := buildSSAForTest(t, eligibilitySrc)
	comp := NewCompiler(1, func(*types.Package) string { return "" })

	qt.Assert(t, qt.IsNotNil(comp.Eligible(ssaPkg.Func("closure"))))
	qt.Assert(t, qt.Equals(len(comp.Program().Funcs), 0))
	qt.Assert(t, qt.Equals(comp.Program().summary(), "0 virtual function(s), 0 native(s), 0 byte(s) of bytecode"))
}

func TestCompileProducesVerifiedProgram(t *testing.T) {
	ssaPkg := buildSSAForTest(t, eligibilitySrc)
	comp := NewCompiler(0xabcdef, func(*types.Package) string { return "" })

	names := []string{"add", "fib", "loop", "mixed", "boolLogic"}
	for _, name := range names {
		comp.Add(ssaPkg.Func(name))
	}
	for _, name := range names {
		_, err := comp.Compile(ssaPkg.Func(name))
		qt.Assert(t, qt.IsNil(err), qt.Commentf("compiling %s", name))
	}

	prog := comp.Program()
	qt.Assert(t, qt.IsNil(prog.CheckAll()))

	// add(1, 2) == 3
	got, err := prog.RunFunc(0, wordOfInt(1), wordOfInt(2))
	qt.Assert(t, qt.IsNil(err))
	qt.Assert(t, qt.DeepEquals(got, []uint64{wordOfInt(3)}))

	// fib(10) == 55, exercising OpCallV recursion.
	got, err = prog.RunFunc(1, wordOfInt(10))
	qt.Assert(t, qt.IsNil(err))
	qt.Assert(t, qt.DeepEquals(got, []uint64{wordOfInt(55)}))

	// loop(100) uses phi nodes. It is not in names above, so compile it on its
	// own compiler to keep indices obvious.
	comp2 := NewCompiler(0xabcdef, func(*types.Package) string { return "" })
	comp2.Add(ssaPkg.Func("loop"))
	_, err = comp2.Compile(ssaPkg.Func("loop"))
	qt.Assert(t, qt.IsNil(err))
	got, err = comp2.Program().RunFunc(0, wordOfInt(100))
	qt.Assert(t, qt.IsNil(err))
	qt.Assert(t, qt.DeepEquals(got, []uint64{wordOfInt(4950)}))

	// mixed(3, 4, 9.0, 7) == (19, 4.5)
	got, err = prog.RunFunc(3, wordOfInt(3), wordOfInt(4), floatBits(9.0), wordOfInt(7))
	qt.Assert(t, qt.IsNil(err))
	qt.Assert(t, qt.DeepEquals(got, []uint64{wordOfInt(19), floatBits(4.5)}))

	// boolLogic(true, false) == true
	got, err = prog.RunFunc(4, 1, 0)
	qt.Assert(t, qt.IsNil(err))
	qt.Assert(t, qt.DeepEquals(got, []uint64{1}))
}

// TestNativeBridge checks that a call to a real function is lowered to a bridge
// whose body names the function and converts between words and its real type.
func TestNativeBridge(t *testing.T) {
	ssaPkg := buildSSAForTest(t, eligibilitySrc)
	comp := NewCompiler(7, func(*types.Package) string { return "" })
	comp.Add(ssaPkg.Func("callsNative"))
	_, err := comp.Compile(ssaPkg.Func("callsNative"))
	qt.Assert(t, qt.IsNil(err))

	natives := comp.Program().Natives
	qt.Assert(t, qt.Equals(len(natives), 1))
	qt.Assert(t, qt.Equals(natives[0].GoName, "nativeMul"))
	qt.Assert(t, qt.StringContains(natives[0].Bridge, "nativeMul("))
	qt.Assert(t, qt.DeepEquals(natives[0].Params, []ValType{TypeInt, TypeInt}))
	qt.Assert(t, qt.DeepEquals(natives[0].Results, []ValType{TypeInt}))
}
