package vm

import (
	"math"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"

	"github.com/go-quicktest/qt"
)

// runEmitted compiles a generated program in a temporary module and returns its
// stdout. The emitted runtime is deliberately a complete, self-contained Go
// program so this test exercises exactly what garble would write into a
// package.
func runEmitted(t *testing.T, p *Program, mainBody string) string {
	t.Helper()

	opts := DefaultEmitterOptions()
	opts.PackageName = "main"
	runtimeSrc, err := p.Emit(opts)
	qt.Assert(t, qt.IsNil(err))

	dir := t.TempDir()
	writeFile := func(name, content string) {
		t.Helper()
		qt.Assert(t, qt.IsNil(os.WriteFile(filepath.Join(dir, name), []byte(content), 0o666)))
	}
	writeFile("go.mod", "module vmtest\n\ngo 1.21\n")
	writeFile("runtime.go", string(runtimeSrc))
	writeFile("main.go", "package main\n\nimport \"fmt\"\n\nfunc main() {\n"+mainBody+"\n\t_ = fmt.Sprint\n}\n")

	cmd := exec.Command("go", "run", ".")
	cmd.Dir = dir
	cmd.Env = append(os.Environ(), "GOFLAGS=-mod=mod", "GOTOOLCHAIN=local")
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("generated program failed: %v\n%s\n--- runtime ---\n%s\n--- main ---\n%s",
			err, out, runtimeSrc, mainBody)
	}
	return string(out)
}

// TestInterpreterMatchesEmitted is the core equivalence guarantee: for a set of
// programs that exercise every arithmetic, comparison and control-flow
// instruction, the reference interpreter and the emitted Go runtime must
// produce identical results.
func TestInterpreterMatchesEmitted(t *testing.T) {
	cases := []struct {
		name string
		prog func() (*Program, []uint64) // program and its arguments
	}{
		{"add", func() (*Program, []uint64) {
			b := NewBuilder()
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpLoadLocal, 1)
			b.Emit(OpAddI, 0)
			b.Emit(OpReturn, 1)
			return singleFunc(b, 2, []ValType{TypeInt, TypeInt}, []ValType{TypeInt}), []uint64{40, 2}
		}},
		{"signed-vs-unsigned-div", func() (*Program, []uint64) {
			// (a / b) and (a % b) computed both signed and unsigned.
			b := NewBuilder()
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpLoadLocal, 1)
			b.Emit(OpDivU, 0)
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpLoadLocal, 1)
			b.Emit(OpDivI, 0)
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpLoadLocal, 1)
			b.Emit(OpRemU, 0)
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpLoadLocal, 1)
			b.Emit(OpRemI, 0)
			b.Emit(OpReturn, 4)
			return singleFunc(b, 2, []ValType{TypeInt, TypeInt}, []ValType{TypeInt, TypeInt, TypeInt, TypeInt}), []uint64{wordOfInt(-17), 5}
		}},
		{"shifts", func() (*Program, []uint64) {
			b := NewBuilder()
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpLoadLocal, 1)
			b.Emit(OpShl, 0)
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpLoadLocal, 1)
			b.Emit(OpShr, 0)
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpLoadLocal, 1)
			b.Emit(OpShrU, 0)
			b.Emit(OpReturn, 3)
			return singleFunc(b, 2, []ValType{TypeInt, TypeInt}, []ValType{TypeInt, TypeInt, TypeInt}), []uint64{wordOfInt(-256), 3}
		}},
		{"floats", func() (*Program, []uint64) {
			b := NewBuilder()
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpLoadLocal, 1)
			b.Emit(OpAddF, 0)
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpLoadLocal, 1)
			b.Emit(OpDivF, 0)
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpLoadLocal, 1)
			b.Emit(OpLtF, 0)
			b.Emit(OpReturn, 3)
			return singleFunc(b, 2, []ValType{TypeFloat, TypeFloat}, []ValType{TypeFloat, TypeFloat, TypeInt}),
				[]uint64{floatBits(1.5), floatBits(2.25)}
		}},
		{"convert", func() (*Program, []uint64) {
			b := NewBuilder()
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpConvert, MakeConvertOperand(KindInt, 64, KindInt, 32))
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpConvert, MakeConvertOperand(KindInt, 64, KindF64, 64))
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpConvert, MakeConvertOperand(KindInt, 64, KindUint, 64))
			b.Emit(OpReturn, 3)
			return singleFunc(b, 1, []ValType{TypeInt}, []ValType{TypeInt, TypeFloat, TypeInt}), []uint64{wordOfInt(-5)}
		}},
		{"branch-loop", func() (*Program, []uint64) {
			// Sum 1..n with a loop.
			// locals: 0=n, 1=sum, 2=i
			b := NewBuilder()
			b.Emit(OpConst, 0)
			b.Emit(OpStoreLocal, 1)
			b.Emit(OpConst, 1)
			b.Emit(OpStoreLocal, 2)
			loop := b.Len()
			b.Emit(OpLoadLocal, 2)
			b.Emit(OpLoadLocal, 0)
			b.Emit(OpGtI, 0)
			done := b.Emit(OpJumpIfNotZero, 0)
			b.Emit(OpLoadLocal, 1)
			b.Emit(OpLoadLocal, 2)
			b.Emit(OpAddI, 0)
			b.Emit(OpStoreLocal, 1)
			b.Emit(OpLoadLocal, 2)
			b.Emit(OpConst, 1)
			b.Emit(OpAddI, 0)
			b.Emit(OpStoreLocal, 2)
			b.Emit(OpJump, int64(loop))
			b.Patch(done, int64(b.Len()))
			b.Emit(OpLoadLocal, 1)
			b.Emit(OpReturn, 1)
			return singleFunc(b, 3, []ValType{TypeInt}, []ValType{TypeInt}), []uint64{10}
		}},
		{"virtual-call", func() (*Program, []uint64) {
			// func double(x) { return x+x }; func quad(x) { return double(double(x)) }
			double := NewBuilder()
			double.Emit(OpLoadLocal, 0)
			double.Emit(OpLoadLocal, 0)
			double.Emit(OpAddI, 0)
			double.Emit(OpReturn, 1)

			// double lives at index 1, so quad calls it twice.
			quad := NewBuilder()
			quad.Emit(OpLoadLocal, 0)
			quad.Emit(OpCallV, 1)
			quad.Emit(OpCallV, 1)
			quad.Emit(OpReturn, 1)

			p := &Program{Key: 0x1234, Funcs: []*Function{
				{Name: "quad", Params: []ValType{TypeInt}, Results: []ValType{TypeInt}, NumLocals: 1, LocalTypes: []ValType{TypeInt}, Code: quad.Encode(0x1234)},
				{Name: "double", Params: []ValType{TypeInt}, Results: []ValType{TypeInt}, NumLocals: 1, LocalTypes: []ValType{TypeInt}, Code: double.Encode(0x1234)},
			}}
			return p, []uint64{7}
		}},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			prog, args := tc.prog()
			qt.Assert(t, qt.IsNil(prog.Verify()))

			got, err := prog.Run(args...)
			qt.Assert(t, qt.IsNil(err))
			want := wordsToLiteral(got)

			// Build a main that calls the machine and prints every word.
			var sb strings.Builder
			sb.WriteString("\tr := _vmp_Run(0, []uint64{")
			for i, a := range args {
				if i > 0 {
					sb.WriteString(", ")
				}
				sb.WriteString(strconv.FormatUint(a, 10))
			}
			sb.WriteString("})\n")
			for i := range got {
				sb.WriteString("\tfmt.Println(r[" + strconv.Itoa(i) + "])\n")
			}
			out := runEmitted(t, prog, sb.String())
			gotEmitted := strings.Fields(strings.TrimSpace(out))
			qt.Assert(t, qt.DeepEquals(gotEmitted, strings.Fields(want)))
		})
	}
}

// singleFunc wraps a builder into a one-function program.
func singleFunc(b *Builder, numLocals int, params, results []ValType) *Program {
	key := uint64(0x9e3779b97f4a7c15)
	localTypes := make([]ValType, numLocals)
	for i := range localTypes {
		localTypes[i] = TypeAny
	}
	copy(localTypes, params)
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

func floatBits(f float64) uint64 {
	return math.Float64bits(f)
}

func wordOfInt(v int64) uint64 { return uint64(v) }

func wordsToLiteral(words []uint64) string {
	var sb strings.Builder
	for _, w := range words {
		sb.WriteString(strconv.FormatUint(w, 10))
		sb.WriteString("\n")
	}
	return sb.String()
}
