package vm

import (
	"fmt"
	"go/types"
	"strings"
)

// GenFunc describes a virtualized function that must be re-emitted into the
// generated file as an ordinary Go wrapper with its original name and
// signature.
//
// The wrapper converts its typed arguments to machine words, runs the virtual
// function and converts the word results back. Because the wrapper keeps the
// original declaration's exact type, every existing caller keeps working
// unchanged, which is what makes virtualization invisible to the rest of the
// program.
type GenFunc struct {
	// Name is the function's unqualified Go identifier.
	Name string
	// Sig is the function's signature. Every parameter and result must be a
	// single machine word; the compiler rejects anything else before it is
	// added here.
	Sig *types.Signature
	// Index is the function's index in the program, i.e. the argument to the
	// generated run entry point.
	Index int
	// Qualifier renders a package as the identifier the generated file uses for
	// it. It must agree with the qualifier used when the program was compiled so
	// that native bridges and wrapper signatures name the same imports.
	Qualifier types.Qualifier
}

// EmitPackage renders a complete Go source file for the program: the runtime,
// the native bridges and one wrapper per virtualized function.
//
// The caller is responsible for the file's package name (in EmitterOptions) and
// for registering every import named by opts.Imports with the rest of the
// build. The file is formatted, so callers can write it out verbatim.
func (p *Program) EmitPackage(opts EmitterOptions, funcs []GenFunc) ([]byte, error) {
	if opts.Prefix == "" {
		return nil, fmt.Errorf("vm: emitter prefix must not be empty")
	}
	decls, err := p.emitDecls(opts)
	if err != nil {
		return nil, err
	}

	var sb strings.Builder
	for _, f := range funcs {
		wrap, err := emitWrapper(opts.Prefix, f)
		if err != nil {
			return nil, err
		}
		sb.WriteString("\n")
		sb.WriteString(wrap)
	}
	return p.assembleFile(opts, decls, sb.String())
}

// emitWrapper renders one wrapper function.
func emitWrapper(prefix string, f GenFunc) (string, error) {
	if f.Sig == nil {
		return "", fmt.Errorf("vm: virtualized function %s has no signature", f.Name)
	}
	qual := f.Qualifier
	if qual == nil {
		qual = func(*types.Package) string { return "" }
	}

	params := make([]string, 0, f.Sig.Params().Len())
	words := make([]string, 0, f.Sig.Params().Len())
	for i := range f.Sig.Params().Len() {
		pv := f.Sig.Params().At(i)
		info, ok := NumInfoOf(pv.Type())
		if !ok {
			return "", fmt.Errorf("vm: parameter %d of %s has non-word type %s",
				i, f.Name, types.TypeString(pv.Type(), qual))
		}
		name := fmt.Sprintf("p%d", i)
		params = append(params, name+" "+types.TypeString(pv.Type(), qual))
		words = append(words, wordFromExpr(prefix, name, info))
	}

	results := make([]string, 0, f.Sig.Results().Len())
	for i := range f.Sig.Results().Len() {
		rv := f.Sig.Results().At(i)
		if _, ok := NumInfoOf(rv.Type()); !ok {
			return "", fmt.Errorf("vm: result %d of %s has non-word type %s",
				i, f.Name, types.TypeString(rv.Type(), qual))
		}
		results = append(results, types.TypeString(rv.Type(), qual))
	}

	var sb strings.Builder
	fmt.Fprintf(&sb, "func %s(%s)", f.Name, strings.Join(params, ", "))
	switch len(results) {
	case 0:
	case 1:
		fmt.Fprintf(&sb, " %s", results[0])
	default:
		fmt.Fprintf(&sb, " (%s)", strings.Join(results, ", "))
	}
	sb.WriteString(" {\n")

	call := fmt.Sprintf("%sRun(%d, []uint64{%s})", prefix, f.Index, strings.Join(words, ", "))
	if len(results) == 0 {
		sb.WriteString("\t" + call + "\n")
	} else {
		fmt.Fprintf(&sb, "\tr := %s\n", call)
		rets := make([]string, 0, len(results))
		for i := range results {
			info, _ := NumInfoOf(f.Sig.Results().At(i).Type())
			rets = append(rets, exprFromWord(prefix, fmt.Sprintf("r[%d]", i), info, results[i]))
		}
		fmt.Fprintf(&sb, "\treturn %s\n", strings.Join(rets, ", "))
	}
	sb.WriteString("}\n")
	return sb.String(), nil
}

// wordFromExpr renders the Go expression that converts a typed value to its
// canonical machine word. Integers are extended to 64 bits, floats are
// reinterpreted as bits and booleans become 0 or 1.
func wordFromExpr(prefix, expr string, info NumInfo) string {
	if info.Bool {
		return prefix + "BoolToWord(bool(" + expr + "))"
	}
	switch info.Kind {
	case KindInt, KindUint:
		return "uint64(" + expr + ")"
	case KindF32:
		return "uint64(" + prefix + "F32bits(float32(" + expr + ")))"
	case KindF64:
		return prefix + "F64bits(float64(" + expr + "))"
	}
	panic("vm: bad numeric kind")
}

// exprFromWord renders the Go expression that converts a machine word back to
// the named Go type.
func exprFromWord(prefix, word string, info NumInfo, typeExpr string) string {
	if info.Bool {
		return typeExpr + "(" + prefix + "WordToBool(" + word + "))"
	}
	switch info.Kind {
	case KindInt, KindUint:
		return typeExpr + "(" + word + ")"
	case KindF32:
		return typeExpr + "(" + prefix + "F32frombits(uint32(" + word + ")))"
	case KindF64:
		return typeExpr + "(" + prefix + "F64frombits(" + word + "))"
	}
	panic("vm: bad numeric kind")
}
