package vm

import (
	"fmt"
	"go/constant"
	"go/token"
	"go/types"
	"math"
	"sort"
	"strings"

	"golang.org/x/tools/go/ssa"
)

// UnsupportedError explains why a function cannot be virtualized. It is a
// normal, expected outcome: the caller falls back to leaving the function in
// its native form, which is always semantically safe.
type UnsupportedError struct {
	// Func is the name of the rejected function.
	Func string
	// Instr is the offending instruction, when the rejection is tied to one.
	Instr string
	// Reason is a human-readable explanation naming the construct and the rule.
	Reason string
}

func (e *UnsupportedError) Error() string {
	if e.Instr != "" {
		return fmt.Sprintf("cannot virtualize %s: %s (%s)", e.Func, e.Reason, e.Instr)
	}
	return fmt.Sprintf("cannot virtualize %s: %s", e.Func, e.Reason)
}

// numTypeParams returns the number of type parameters in a list that may be
// nil, as go/types reports for non-generic functions.
func numTypeParams(list *types.TypeParamList) int {
	if list == nil {
		return 0
	}
	return list.Len()
}

func unsupportedf(fn *ssa.Function, reason string, args ...any) error {
	return &UnsupportedError{Func: fn.String(), Reason: fmt.Sprintf(reason, args...)}
}

func unsupportedInstr(fn *ssa.Function, instr ssa.Instruction, reason string, args ...any) error {
	return &UnsupportedError{Func: fn.String(), Instr: instr.String(), Reason: fmt.Sprintf(reason, args...)}
}

// NumInfo describes the machine-level view of a Go numeric type.
type NumInfo struct {
	// Type is the abstract operand type used by the verifier.
	Type ValType
	// Kind is the conversion kind (KindInt, KindUint, KindF32 or KindF64).
	Kind int
	// Bits is the type's width in bits. It is 1 for booleans, which are stored
	// as the words 0 and 1 and never participate in numeric conversion.
	Bits int
	// Bool reports whether the type is a boolean.
	Bool bool
}

// NumInfoOf reports the machine-level view of t, if t is a type the virtual
// machine can represent as a single word.
func NumInfoOf(t types.Type) (NumInfo, bool) {
	t = types.Unalias(t)
	basic, ok := t.Underlying().(*types.Basic)
	if !ok {
		return NumInfo{}, false
	}
	info := basic.Info()
	switch {
	case info&types.IsBoolean != 0:
		return NumInfo{Type: TypeInt, Kind: KindUint, Bits: 1, Bool: true}, true
	case info&types.IsInteger != 0:
		bits := basicBits(basic)
		kind := KindInt
		if basic.Info()&types.IsUnsigned != 0 {
			kind = KindUint
		}
		return NumInfo{Type: TypeInt, Kind: kind, Bits: bits}, true
	case info&types.IsFloat != 0:
		if basic.Kind() == types.Float32 {
			return NumInfo{Type: TypeFloat, Kind: KindF32, Bits: 32}, true
		}
		return NumInfo{Type: TypeFloat, Kind: KindF64, Bits: 64}, true
	}
	return NumInfo{}, false
}

// basicBits reports the width in bits of an integer basic type. The virtual
// machine is a 64-bit word machine, so int, uint and uintptr are treated as
// 64-bit; the fixed-width types are exact because every operation is normalized
// back to its own width.
func basicBits(b *types.Basic) int {
	switch b.Kind() {
	case types.Int8, types.Uint8:
		return 8
	case types.Int16, types.Uint16:
		return 16
	case types.Int32, types.Uint32:
		return 32
	default:
		return 64
	}
}

// WordType reports whether t is representable as a single virtual machine word,
// and if so its abstract operand type.
func WordType(t types.Type) (ValType, bool) {
	info, ok := NumInfoOf(t)
	if !ok {
		return TypeAny, false
	}
	return info.Type, true
}

// Compiler lowers eligible SSA functions into a shared virtual Program.
//
// A Compiler is used for one package: the caller decides which functions are
// candidates, registers them with Add, and then compiles each with Compile.
// Registration must happen before compilation so that calls between virtualized
// functions can be resolved to OpCallV.
type Compiler struct {
	prog       *Program
	importName func(*types.Package) string
	prefix     string // generated identifier prefix, e.g. "_vmp_"
	funcIndex  map[*ssa.Function]int
	funcs      []*ssa.Function // registered functions in index order
	nativeIdx  map[string]int
}

// NewCompiler returns a Compiler that emits into a fresh Program with the given
// decode key. importName resolves a package to the identifier the generated
// code must use to refer to it; it may return "" for the package being
// generated.
func NewCompiler(key uint64, importName func(*types.Package) string) *Compiler {
	return &Compiler{
		prog:       &Program{Key: key, Hardening: newHardening(key)},
		importName: importName,
		prefix:     "_vmp_",
		funcIndex:  make(map[*ssa.Function]int),
		nativeIdx:  make(map[string]int),
	}
}

// Program returns the program being built. It is only complete once every
// registered function has been compiled.
func (c *Compiler) Program() *Program {
	// Decoy native bridges: never referenced by live OpCallN, but present in tables.
	if c.prog.Hardening != nil && len(c.prog.DecoyNatives) == 0 {
		seed := c.prog.Key
		for i := 0; i < 3; i++ {
			seed = mix64(seed + uint64(i))
			c.prog.DecoyNatives = append(c.prog.DecoyNatives, &NativeFunc{
				GoName: fmt.Sprintf("_vmp_decoy_%d", i),
				Params: []ValType{TypeInt},
				Results: []ValType{TypeInt},
				Bridge: "return []uint64{a[0]}",
			})
		}
	}
	c.prog.ComputeIntegrity()
	return c.prog
}

// SetPrefix sets the identifier prefix used by the generated code's runtime
// helpers. It must match the EmitterOptions.Prefix used to emit the program, so
// that native bridges reference the same helpers.
func (c *Compiler) SetPrefix(prefix string) {
	if prefix != "" {
		c.prefix = prefix
	}
}

// Add registers fn as a virtual function and returns its index, which is the
// operand used by OpCallV. Adding the same function twice is a no-op.
func (c *Compiler) Add(fn *ssa.Function) int {
	if idx, ok := c.funcIndex[fn]; ok {
		return idx
	}
	idx := len(c.prog.Funcs)
	c.prog.Funcs = append(c.prog.Funcs, c.stub(fn))
	c.funcIndex[fn] = idx
	c.funcs = append(c.funcs, fn)
	return idx
}

// stub returns a placeholder function carrying fn's signature. It lets the
// verifier resolve OpCallV to a function that has not been compiled yet, which
// is necessary for recursion and for calls between virtualized functions.
func (c *Compiler) stub(fn *ssa.Function) *Function {
	params := make([]ValType, 0, len(fn.Params))
	localTypes := make([]ValType, 0, len(fn.Params))
	for _, p := range fn.Params {
		t, _ := WordType(p.Type())
		params = append(params, t)
		localTypes = append(localTypes, t)
	}
	results := fn.Signature.Results()
	resultTypes := make([]ValType, 0, results.Len())
	for i := range results.Len() {
		t, _ := WordType(results.At(i).Type())
		resultTypes = append(resultTypes, t)
	}
	return &Function{
		Name:       fn.String(),
		Params:     params,
		Results:    resultTypes,
		NumLocals:  len(params),
		LocalTypes: localTypes,
	}
}

// Funcs returns the registered functions in index order, so the caller can emit
// one wrapper per virtual function.
func (c *Compiler) Funcs() []*ssa.Function { return c.funcs }

// Index returns the virtual index of fn and whether it was registered.
func (c *Compiler) Index(fn *ssa.Function) (int, bool) {
	idx, ok := c.funcIndex[fn]
	return idx, ok
}

// Eligible reports whether fn can be virtualized, returning a descriptive error
// when it cannot. Eligibility is a pure function of fn and the program's
// already-registered functions; it never modifies state.
func (c *Compiler) Eligible(fn *ssa.Function) error {
	return c.analyze(fn)
}

// Compile lowers fn into bytecode and stores it in the program. fn must already
// have been registered with Add. It returns the verified function.
func (c *Compiler) Compile(fn *ssa.Function) (*Function, error) {
	idx, ok := c.funcIndex[fn]
	if !ok {
		return nil, fmt.Errorf("vm: function %s was not registered with Add", fn.String())
	}
	if err := c.analyze(fn); err != nil {
		return nil, err
	}

	fc := &funcCompiler{
		c:          c,
		fn:         fn,
		slotOf:     make(map[ssa.Value]int),
		localTypes: nil,
		blockStart: make(map[*ssa.BasicBlock]int),
	}
	if err := fc.run(); err != nil {
		return nil, err
	}

	out := &Function{
		Name:       fn.String(),
		Params:     fc.paramTypes,
		Results:    fc.resultTypes,
		NumLocals:  fc.numLocals,
		LocalTypes: fc.localTypes,
		Code:       fc.code,
	}
	if err := c.prog.verifyFunc(out); err != nil {
		return nil, err
	}
	if c.prog.Hardening != nil {
		c.prog.Hardening.InitSlotPerm(out.NumLocals)
		c.prog.Hardening.BuildBlockHashes(out, c.prog.Key)
	}
	c.prog.Funcs[idx] = out
	return out, nil
}

// analyze decides whether fn is in the supported subset. It reports the first
// unsupported construct it finds, so the message is actionable.
func (c *Compiler) analyze(fn *ssa.Function) error {
	if fn.Parent() != nil {
		return unsupportedf(fn, "closures and anonymous functions are not supported")
	}
	if fn.Signature.Recv() != nil {
		// A method's receiver is its first SSA parameter, but re-emitting it as a
		// package-level wrapper would lose the receiver. Reject methods rather
		// than miscompile them.
		return unsupportedf(fn, "methods are not supported; move the body into a function")
	}
	if name := fn.Name(); name == "init" || name == "main" {
		return unsupportedf(fn, "the %s function is not supported", name)
	}
	if len(fn.FreeVars) > 0 {
		return unsupportedf(fn, "function has %d captured variable(s); closures are not supported", len(fn.FreeVars))
	}
	if numTypeParams(fn.TypeParams()) > 0 || len(fn.TypeArgs()) > 0 {
		return unsupportedf(fn, "generic functions are not supported")
	}
	if fn.Signature.Variadic() {
		return unsupportedf(fn, "variadic functions are not supported")
	}
	if len(fn.Blocks) == 0 {
		return unsupportedf(fn, "function has no body")
	}

	// Every parameter and result must be a single machine word. Pointer,
	// interface, slice, map, string, channel and struct types are rejected
	// because they cannot be stored on the operand stack without becoming
	// invisible to the garbage collector.
	for i := range fn.Params {
		if _, ok := NumInfoOf(fn.Params[i].Type()); !ok {
			return unsupportedf(fn, "parameter %s has unsupported type %s",
				fn.Params[i].Name(), types.TypeString(fn.Params[i].Type(), nil))
		}
	}
	results := fn.Signature.Results()
	for i := range results.Len() {
		if _, ok := NumInfoOf(results.At(i).Type()); !ok {
			return unsupportedf(fn, "result %d has unsupported type %s",
				i, types.TypeString(results.At(i).Type(), nil))
		}
	}

	for _, blk := range fn.Blocks {
		for _, instr := range blk.Instrs {
			if err := c.analyzeInstr(fn, instr); err != nil {
				return err
			}
		}
	}
	return nil
}

func (c *Compiler) analyzeInstr(fn *ssa.Function, instr ssa.Instruction) error {
	switch instr := instr.(type) {
	case *ssa.DebugRef, *ssa.RunDefers:
		// DebugRef carries source position information only, and RunDefers is a
		// no-op because Defer instructions are rejected below.
		return nil

	case *ssa.Alloc:
		if instr.Heap {
			return unsupportedInstr(fn, instr, "allocated value escapes to the heap; taking its address is not supported")
		}
		ptr, ok := instr.Type().Underlying().(*types.Pointer)
		if !ok {
			return unsupportedInstr(fn, instr, "local has unsupported type")
		}
		if _, ok := NumInfoOf(ptr.Elem()); !ok {
			return unsupportedInstr(fn, instr, "local has unsupported type")
		}
		return nil

	case *ssa.Store:
		if _, ok := instr.Addr.(*ssa.Alloc); !ok {
			return unsupportedInstr(fn, instr, "store through a pointer other than a local variable is not supported")
		}
		return nil

	case *ssa.BinOp:
		return c.analyzeBinOp(fn, instr)

	case *ssa.UnOp:
		return c.analyzeUnOp(fn, instr)

	case *ssa.Convert, *ssa.ChangeType:
		if _, ok := NumInfoOf(instr.(ssa.Value).Type()); !ok {
			return unsupportedInstr(fn, instr, "conversion to an unsupported type")
		}
		return nil

	case *ssa.Phi:
		if _, ok := NumInfoOf(instr.Type()); !ok {
			return unsupportedInstr(fn, instr, "phi of an unsupported type")
		}
		return nil

	case *ssa.Call:
		return c.analyzeCall(fn, instr)

	case *ssa.Extract:
		if _, ok := NumInfoOf(instr.Type()); !ok {
			return unsupportedInstr(fn, instr, "extracted value of an unsupported type")
		}
		return nil

	case *ssa.If:
		if _, ok := NumInfoOf(instr.Cond.Type()); !ok {
			return unsupportedInstr(fn, instr, "condition of an unsupported type")
		}
		return nil

	case *ssa.Jump:
		return nil

	case *ssa.Return:
		return nil

	default:
		return unsupportedInstr(fn, instr, "instruction is outside the supported subset")
	}
}

func (c *Compiler) analyzeBinOp(fn *ssa.Function, instr *ssa.BinOp) error {
	xInfo, ok := NumInfoOf(instr.X.Type())
	if !ok {
		return unsupportedInstr(fn, instr, "left operand has unsupported type")
	}
	yInfo, ok := NumInfoOf(instr.Y.Type())
	if !ok {
		return unsupportedInstr(fn, instr, "right operand has unsupported type")
	}
	if _, ok := NumInfoOf(instr.Type()); !ok {
		return unsupportedInstr(fn, instr, "result has unsupported type")
	}
	// Floating-point arithmetic and comparison are performed at float64
	// precision. float32 values are promoted for the operation and the result
	// is stored back according to the result type (float32 or float64). This
	// keeps the single TypeFloat word model while supporting both widths.
	switch instr.Op {
	case token.ADD, token.SUB, token.MUL:
		if xInfo.Type != yInfo.Type {
			return unsupportedInstr(fn, instr, "mixed %s and %s operands", xInfo.Type, yInfo.Type)
		}
		return nil
	case token.QUO, token.REM:
		// Integer remainder and floating-point remainder (OpRemF / math.Mod) are
		// both supported.
		if xInfo.Type != yInfo.Type {
			return unsupportedInstr(fn, instr, "mixed %s and %s operands", xInfo.Type, yInfo.Type)
		}
		return nil
	case token.AND, token.OR, token.XOR:
		if xInfo.Type == TypeFloat {
			return unsupportedInstr(fn, instr, "bitwise operation on floating point values")
		}
		return nil
	case token.SHL, token.SHR:
		if xInfo.Type == TypeFloat || yInfo.Type == TypeFloat {
			return unsupportedInstr(fn, instr, "shift of a floating point value")
		}
		return nil
	case token.EQL, token.NEQ, token.LSS, token.LEQ, token.GTR, token.GEQ:
		if xInfo.Type != yInfo.Type {
			return unsupportedInstr(fn, instr, "comparison of %s with %s", xInfo.Type, yInfo.Type)
		}
		return nil
	}
	return unsupportedInstr(fn, instr, "unsupported binary operator %s", instr.Op)
}

func (c *Compiler) analyzeUnOp(fn *ssa.Function, instr *ssa.UnOp) error {
	xInfo, ok := NumInfoOf(instr.X.Type())
	switch instr.Op {
	case token.MUL:
		// Dereference of a local variable's address: the only memory access the
		// virtual machine supports, and the only one that never leaves a real
		// pointer in a stack word.
		if _, ok := instr.X.(*ssa.Alloc); !ok {
			return unsupportedInstr(fn, instr, "dereference of a pointer other than a local variable is not supported")
		}
		return nil
	case token.SUB, token.XOR, token.NOT:
		if !ok {
			return unsupportedInstr(fn, instr, "operand has unsupported type")
		}
		if instr.Op == token.XOR && xInfo.Type == TypeFloat {
			return unsupportedInstr(fn, instr, "bitwise complement of a floating point value")
		}
		return nil
	}
	return unsupportedInstr(fn, instr, "unsupported unary operator %s", instr.Op)
}

func (c *Compiler) analyzeCall(fn *ssa.Function, instr *ssa.Call) error {
	common := instr.Call
	if common.IsInvoke() {
		return unsupportedInstr(fn, instr, "interface method call is not supported")
	}
	switch callee := common.Value.(type) {
	case *ssa.Function:
		if _, ok := c.funcIndex[callee]; ok {
			return nil // a call between virtualized functions
		}
		return c.analyzeNativeCallee(fn, instr, callee)
	case *ssa.Builtin:
		return unsupportedInstr(fn, instr, "call to builtin %s is not supported", callee.Name())
	default:
		return unsupportedInstr(fn, instr, "indirect call through a function value is not supported")
	}
}

// analyzeNativeCallee decides whether a call to a real Go function can be
// bridged. Only package-level functions with word-typed parameters and results
// qualify, because the bridge must be able to name and convert them.
func (c *Compiler) analyzeNativeCallee(fn *ssa.Function, instr ssa.Instruction, callee *ssa.Function) error {
	if callee.Parent() != nil {
		return unsupportedInstr(fn, instr, "call to a closure is not supported")
	}
	if callee.Object() == nil || callee.Object().Pkg() == nil {
		return unsupportedInstr(fn, instr, "call to a function with no package is not supported")
	}
	sig := callee.Signature
	if sig.Recv() != nil {
		return unsupportedInstr(fn, instr, "call to method %s is not supported", callee.Name())
	}
	if sig.Variadic() {
		return unsupportedInstr(fn, instr, "call to variadic function %s is not supported", callee.Name())
	}
	if numTypeParams(callee.TypeParams()) > 0 || len(callee.TypeArgs()) > 0 {
		return unsupportedInstr(fn, instr, "call to generic function %s is not supported", callee.Name())
	}
	for i := range sig.Params().Len() {
		if _, ok := NumInfoOf(sig.Params().At(i).Type()); !ok {
			return unsupportedInstr(fn, instr, "parameter %d of %s has unsupported type %s",
				i, callee.Name(), types.TypeString(sig.Params().At(i).Type(), nil))
		}
	}
	for i := range sig.Results().Len() {
		if _, ok := NumInfoOf(sig.Results().At(i).Type()); !ok {
			return unsupportedInstr(fn, instr, "result %d of %s has unsupported type %s",
				i, callee.Name(), types.TypeString(sig.Results().At(i).Type(), nil))
		}
	}
	return nil
}

// nativeFunc returns the index of the bridge for callee, adding one if needed.
func (c *Compiler) nativeFunc(callee *ssa.Function) (int, error) {
	name, err := c.goFuncName(callee)
	if err != nil {
		return 0, err
	}
	if idx, ok := c.nativeIdx[name]; ok {
		return idx, nil
	}

	sig := callee.Signature
	var params, results []ValType
	for i := range sig.Params().Len() {
		t, _ := WordType(sig.Params().At(i).Type())
		params = append(params, t)
	}
	for i := range sig.Results().Len() {
		t, _ := WordType(sig.Results().At(i).Type())
		results = append(results, t)
	}

	bridge, err := c.nativeBridge(name, sig)
	if err != nil {
		return 0, err
	}

	idx := len(c.prog.Natives)
	c.prog.Natives = append(c.prog.Natives, &NativeFunc{
		GoName:  name,
		Params:  params,
		Results: results,
		Bridge:  bridge,
	})
	c.nativeIdx[name] = idx
	return idx, nil
}

// goFuncName renders the identifier the generated code must use to call callee.
func (c *Compiler) goFuncName(callee *ssa.Function) (string, error) {
	obj := callee.Object()
	if obj == nil || obj.Pkg() == nil {
		return "", fmt.Errorf("vm: function %s has no package", callee.String())
	}
	alias := c.importName(obj.Pkg())
	if alias == "" {
		return obj.Name(), nil
	}
	return alias + "." + obj.Name(), nil
}

// nativeBridge renders the body of the bridge function for a native callee. The
// body converts the incoming words to the callee's real parameter types, calls
// it, and converts the results back to words.
func (c *Compiler) nativeBridge(name string, sig *types.Signature) (string, error) {
	qualifier := func(pkg *types.Package) string {
		if pkg == nil {
			return ""
		}
		return c.importName(pkg)
	}

	var args []string
	for i := range sig.Params().Len() {
		pt := sig.Params().At(i).Type()
		info, ok := NumInfoOf(pt)
		if !ok {
			return "", fmt.Errorf("vm: unsupported native parameter type %s", types.TypeString(pt, nil))
		}
		typeExpr := types.TypeString(pt, qualifier)
		word := fmt.Sprintf("a[%d]", i)
		args = append(args, fromWord(c.prefix, word, info, typeExpr))
	}
	call := name + "(" + strings.Join(args, ", ") + ")"

	n := sig.Results().Len()
	if n == 0 {
		return call, nil
	}
	if n == 1 {
		rt := sig.Results().At(0).Type()
		info, _ := NumInfoOf(rt)
		return "return []uint64{" + toWord(c.prefix, call, info, types.TypeString(rt, qualifier)) + "}", nil
	}

	var names, values []string
	for i := range n {
		rt := sig.Results().At(i).Type()
		info, _ := NumInfoOf(rt)
		names = append(names, fmt.Sprintf("r%d", i))
		values = append(values, toWord(c.prefix, fmt.Sprintf("r%d", i), info, types.TypeString(rt, qualifier)))
	}
	return strings.Join(names, ", ") + " := " + call + "; return []uint64{" + strings.Join(values, ", ") + "}", nil
}

// fromWord converts a word to the Go type named by typeExpr.
func fromWord(prefix, word string, info NumInfo, typeExpr string) string {
	if info.Bool {
		return word + " != 0"
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

// toWord converts a Go value of the type named by typeExpr to a word.
func toWord(prefix, expr string, info NumInfo, typeExpr string) string {
	_ = typeExpr
	if info.Bool {
		return "func() uint64 { if " + expr + " { return 1 }; return 0 }()"
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

// ---------------------------------------------------------------------------
// Function body lowering
// ---------------------------------------------------------------------------

type funcCompiler struct {
	c  *Compiler
	fn *ssa.Function

	code []byte

	slotOf     map[ssa.Value]int
	localTypes []ValType
	numLocals  int

	paramTypes  []ValType
	resultTypes []ValType

	blockStart map[*ssa.BasicBlock]int

	b       *Builder
	onStack []ssa.Value
	fixups  []fixup
}

type fixup struct {
	pc     int
	target *ssa.BasicBlock
}

func (fc *funcCompiler) run() error {
	fc.b = NewBuilder()

	// Parameters occupy the first slots of the frame.
	for _, p := range fc.fn.Params {
		fc.assignSlot(p)
	}
	results := fc.fn.Signature.Results()
	for i := range results.Len() {
		info, _ := NumInfoOf(results.At(i).Type())
		fc.resultTypes = append(fc.resultTypes, info.Type)
	}
	for _, p := range fc.fn.Params {
		info, _ := NumInfoOf(p.Type())
		fc.paramTypes = append(fc.paramTypes, info.Type)
	}

	// Pre-assign slots for everything that must live in the frame: local
	// variables, phi nodes and any value that is not consumed immediately.
	for _, blk := range fc.fn.Blocks {
		for _, instr := range blk.Instrs {
			switch instr := instr.(type) {
			case *ssa.Alloc:
				fc.assignSlot(instr)
			case *ssa.Phi:
				fc.assignSlot(instr)
			default:
				if v, ok := instr.(ssa.Value); ok && fc.mustSpill(v) {
					fc.assignSlot(v)
				}
			}
		}
	}

	// Emit every block, recording its start offset for branch resolution.
	for _, blk := range fc.fn.Blocks {
		fc.blockStart[blk] = fc.b.Len()
		if err := fc.compileBlock(blk); err != nil {
			return err
		}
	}

	// Resolve branch targets now that every block has an offset.
	for _, f := range fc.fixups {
		target, ok := fc.blockStart[f.target]
		if !ok {
			return fmt.Errorf("vm: %s: branch to a block that was not emitted", fc.fn.String())
		}
		fc.b.Patch(f.pc, int64(target))
	}

	fc.code = fc.b.EncodeHard(fc.c.prog.Key, fc.c.prog.Hardening)
	return nil
}

// assignSlot gives v a frame slot, growing the frame as needed.
func (fc *funcCompiler) assignSlot(v ssa.Value) int {
	if slot, ok := fc.slotOf[v]; ok {
		return slot
	}
	slot := fc.numLocals
	fc.numLocals++
	fc.slotOf[v] = slot

	var ty ValType = TypeAny
	if info, ok := NumInfoOf(v.Type()); ok {
		ty = info.Type
	}
	for len(fc.localTypes) < fc.numLocals {
		fc.localTypes = append(fc.localTypes, TypeAny)
	}
	fc.localTypes[slot] = ty
	return slot
}

// mustSpill reports whether v has to live in the frame rather than on the
// operand stack.
//
// The compiler is deliberately conservative: every value except a constant is
// assigned a frame slot and stored there as soon as it is produced. Keeping
// values on the operand stack across instruction boundaries is a pure
// optimization, and doing so safely requires reasoning about value ordering
// within a block; spilling avoids a whole class of subtle stack-model bugs at
// the cost of some load/store traffic. Constants are the one exception: they
// are re-materialized with OpConst wherever they are used, so they never need
// a slot.
func (fc *funcCompiler) mustSpill(v ssa.Value) bool {
	if _, ok := v.(*ssa.Const); ok {
		return false
	}
	return true
}

// emit appends an instruction, returning its offset.
func (fc *funcCompiler) emit(op Opcode, arg int64) int { return fc.b.Emit(op, arg) }

// pushResult records that the instruction just emitted left v on the stack.
func (fc *funcCompiler) pushResult(v ssa.Value) {
	fc.onStack = append(fc.onStack, v)
	if !fc.mustSpill(v) {
		return
	}
	slot := fc.slotOf[v]
	fc.emit(OpStoreLocal, int64(slot))
	fc.onStack = fc.onStack[:len(fc.onStack)-1]
}

// indexOfStack reports where v currently sits in the operand-stack model, or -1
// when v is not on the stack.
func (fc *funcCompiler) indexOfStack(v ssa.Value) int {
	for i := len(fc.onStack) - 1; i >= 0; i-- {
		if fc.onStack[i] == v {
			return i
		}
	}
	return -1
}

// load makes v the top of the operand stack.
//
// Constants are re-materialized from their value; every other value is read
// from its frame slot, where it was stored when it was produced.
func (fc *funcCompiler) load(v ssa.Value) {
	if len(fc.onStack) > 0 && fc.onStack[len(fc.onStack)-1] == v {
		return // already the top of the stack
	}
	if c, ok := v.(*ssa.Const); ok {
		word, ok := constWord(c)
		if !ok {
			panic(fmt.Sprintf("vm: internal error: constant %s is not a machine word", c.Name()))
		}
		op := OpConst
		if info, ok := NumInfoOf(v.Type()); ok && info.Type == TypeFloat {
			op = OpConstF
		}
		// Instruction splitting: materialize integer constants via XOR chain
		// (c^k) xor k => c so immediates never appear plaintext in one Const.
		if op == OpConst && fc.c.prog.Hardening != nil && word != 0 {
			for _, part := range SplitConst(int64(word), fc.c.prog.Key, fc.b.Len()) {
				fc.emit(part.Op, part.Arg)
			}
		} else {
			fc.emit(op, int64(word))
		}
		fc.onStack = append(fc.onStack, v)
		return
	}
	slot, ok := fc.slotOf[v]
	if !ok {
		panic(fmt.Sprintf("vm: internal error: value %s has no frame slot", v.Name()))
	}
	fc.emit(OpLoadLocal, int64(slot))
	fc.onStack = append(fc.onStack, v)
}

// consume pops n values from the model of the operand stack.
func (fc *funcCompiler) consume(n int) {
	if n > len(fc.onStack) {
		panic("vm: internal error: operand stack model underflow")
	}
	fc.onStack = fc.onStack[:len(fc.onStack)-n]
}

// ensureEmpty asserts that the operand stack is balanced at a block boundary.
func (fc *funcCompiler) ensureEmpty() {
	if len(fc.onStack) != 0 {
		panic(fmt.Sprintf("vm: internal error: %d value(s) left on the operand stack at a block boundary", len(fc.onStack)))
	}
}

func (fc *funcCompiler) compileBlock(blk *ssa.BasicBlock) error {
	fc.onStack = fc.onStack[:0]

	instrs := blk.Instrs
	for i, instr := range instrs {
		isTerminator := i == len(instrs)-1
		if isTerminator {
			return fc.compileTerminator(blk, instr)
		}
		if err := fc.compileInstr(blk, instr); err != nil {
			return err
		}
	}
	return nil
}

func (fc *funcCompiler) compileInstr(blk *ssa.BasicBlock, instr ssa.Instruction) error {
	switch instr := instr.(type) {
	case *ssa.DebugRef, *ssa.RunDefers:
		return nil

	case *ssa.Alloc:
		// A local variable. Nothing to emit: the slot is the storage, and its
		// initial value is zero, matching Go's zero value for these types.
		return nil

	case *ssa.Store:
		alloc := instr.Addr.(*ssa.Alloc)
		slot := fc.slotOf[alloc]
		// A variable may be assigned values of different concrete types in a
		// way SSA does not unify; store through the slot's declared type so the
		// verifier sees a single type per slot.
		fc.load(instr.Val)
		if info, ok := NumInfoOf(instr.Val.Type()); ok {
			fc.reserveSlots(slot, info.Type)
		}
		fc.emit(OpStoreLocal, int64(slot))
		fc.consume(1)

	case *ssa.BinOp:
		return fc.compileBinOp(instr)

	case *ssa.UnOp:
		return fc.compileUnOp(instr)

	case *ssa.Convert, *ssa.ChangeType:
		return fc.compileConvert(instr)

	case *ssa.Phi:
		// Phi values are assigned by their predecessors; nothing to do here.
		return nil

	case *ssa.Call:
		return fc.compileCall(instr)

	case *ssa.Extract:
		tuple := instr.Tuple
		slot, ok := fc.slotOf[tuple]
		if !ok {
			return unsupportedInstr(fc.fn, instr, "extract of a value that is not stored in the frame")
		}
		// Results of a multi-value call occupy a run of frame slots.
		target := slot + instr.Index
		fc.reserveSlots(target, TypeAny)
		fc.emit(OpLoadLocal, int64(target))
		fc.pushResult(instr)

	default:
		return unsupportedInstr(fc.fn, instr, "instruction is outside the supported subset")
	}
	return nil
}

func (fc *funcCompiler) compileBinOp(instr *ssa.BinOp) error {
	xInfo, _ := NumInfoOf(instr.X.Type())
	yInfo, _ := NumInfoOf(instr.Y.Type())
	resInfo, _ := NumInfoOf(instr.Type())

	op, err := binOpcode(instr.Op, xInfo, yInfo)
	if err != nil {
		return unsupportedInstr(fc.fn, instr, "%s", err)
	}

	fc.load(instr.X)
	fc.load(instr.Y)
	fc.emit(op, 0)
	fc.consume(2)

	// Integer results narrower than 64 bits must wrap to their own width, and
	// the shift count must not be masked to the machine width. Normalizing the
	// result here reproduces Go's per-type overflow and shift semantics exactly.
	if normalize, ok := normalizeOperand(resInfo); ok {
		fc.emit(OpConvert, normalize)
	}
	fc.pushResult(instr)
	return nil
}

func (fc *funcCompiler) compileUnOp(instr *ssa.UnOp) error {
	resInfo, _ := NumInfoOf(instr.Type())
	xInfo, _ := NumInfoOf(instr.X.Type())

	switch instr.Op {
	case token.MUL:
		alloc := instr.X.(*ssa.Alloc)
		fc.emit(OpLoadLocal, int64(fc.slotOf[alloc]))
		fc.pushResult(instr)
		return nil
	case token.SUB:
		fc.load(instr.X)
		if xInfo.Type == TypeFloat {
			fc.emit(OpNegF, 0)
		} else {
			fc.emit(OpNegI, 0)
		}
		fc.consume(1)
	case token.XOR:
		fc.load(instr.X)
		fc.emit(OpNot, 0)
		fc.consume(1)
	case token.NOT:
		fc.load(instr.X)
		fc.emit(OpNotB, 0)
		fc.consume(1)
	default:
		return unsupportedInstr(fc.fn, instr, "unsupported unary operator %s", instr.Op)
	}

	if normalize, ok := normalizeOperand(resInfo); ok {
		fc.emit(OpConvert, normalize)
	}
	fc.pushResult(instr)
	return nil
}

func (fc *funcCompiler) compileConvert(instr ssa.Instruction) error {
	val := instr.(ssa.Value)
	var x ssa.Value
	switch v := instr.(type) {
	case *ssa.Convert:
		x = v.X
	case *ssa.ChangeType:
		x = v.X
	default:
		return unsupportedInstr(fc.fn, instr, "unsupported conversion")
	}
	srcInfo, ok := NumInfoOf(x.Type())
	if !ok {
		return unsupportedInstr(fc.fn, instr, "conversion source has an unsupported type")
	}
	dstInfo, ok := NumInfoOf(val.Type())
	if !ok {
		return unsupportedInstr(fc.fn, instr, "conversion target has an unsupported type")
	}

	// A conversion between identical machine representations is a no-op.
	if srcInfo.Kind == dstInfo.Kind && srcInfo.Bits == dstInfo.Bits {
		fc.load(x)
		fc.pushResult(val)
		return nil
	}

	fc.load(x)
	fc.emit(OpConvert, MakeConvertOperand(srcInfo.Kind, srcInfo.Bits, dstInfo.Kind, dstInfo.Bits))
	fc.consume(1)
	fc.pushResult(val)
	return nil
}

func (fc *funcCompiler) compileCall(instr *ssa.Call) error {
	common := instr.Call
	callee, ok := common.Value.(*ssa.Function)
	if !ok {
		return unsupportedInstr(fc.fn, instr, "indirect call is not supported")
	}

	if idx, ok := fc.c.Index(callee); ok {
		for _, arg := range common.Args {
			fc.load(arg)
		}
		fc.emit(OpCallV, int64(idx))
		fc.consume(len(common.Args))
		fc.pushResults(instr, callee.Signature.Results().Len())
		return nil
	}

	nativeIdx, err := fc.c.nativeFunc(callee)
	if err != nil {
		return err
	}
	for _, arg := range common.Args {
		fc.load(arg)
	}
	fc.emit(OpCallN, int64(nativeIdx))
	fc.consume(len(common.Args))
	fc.pushResults(instr, callee.Signature.Results().Len())
	return nil
}

// pushResults records the results of a call. Multi-value calls occupy a run of
// frame slots so that Extract can read each one.
func (fc *funcCompiler) pushResults(instr ssa.Value, n int) {
	switch n {
	case 0:
		// The call produced no value; nothing to record.
	case 1:
		fc.pushResult(instr)
	default:
		slot := fc.assignSlot(instr)
		for i := 1; i < n; i++ {
			// Reserve the following slots for the remaining results.
			fc.reserveSlots(slot+i, resultTypeAt(instr, i))
		}
		// The results are on the stack with the last one on top, so store them
		// from the top downwards into ascending slot numbers.
		for i := n - 1; i >= 0; i-- {
			fc.emit(OpStoreLocal, int64(slot+i))
		}
		fc.consume(n)
	}
}

// reserveSlots grows the frame so that slot exists and carries the given type.
// An existing TypeAny slot is upgraded; a conflicting type is left alone so the
// verifier reports it.
func (fc *funcCompiler) reserveSlots(slot int, ty ValType) {
	for fc.numLocals <= slot {
		fc.numLocals++
		fc.localTypes = append(fc.localTypes, TypeAny)
	}
	if slot < len(fc.localTypes) {
		if fc.localTypes[slot] == TypeAny || ty == TypeAny {
			if ty != TypeAny {
				fc.localTypes[slot] = ty
			}
		}
	}
}

func resultTypeAt(v ssa.Value, idx int) ValType {
	tuple, ok := v.Type().(*types.Tuple)
	if !ok || idx >= tuple.Len() {
		return TypeAny
	}
	info, ok := NumInfoOf(tuple.At(idx).Type())
	if !ok {
		return TypeAny
	}
	return info.Type
}

func (fc *funcCompiler) compileTerminator(blk *ssa.BasicBlock, instr ssa.Instruction) error {
	switch instr := instr.(type) {
	case *ssa.Jump:
		fc.emitPhiAssignments(blk.Succs[0], blk)
		fc.ensureEmpty()
		pc := fc.emit(OpJump, 0)
		fc.fixups = append(fc.fixups, fixup{pc: pc, target: blk.Succs[0]})
		return nil

	case *ssa.If:
		condSlot := fc.forceToSlot(instr.Cond)
		// Both successors' phi values are assigned before the branch. Each phi
		// variable is read only in its own block, so assigning both is correct.
		// The assignments go first so that they see the values still on the
		// operand stack; the condition is then reloaded from its slot.
		fc.emitPhiAssignments(blk.Succs[0], blk)
		fc.emitPhiAssignments(blk.Succs[1], blk)
		fc.ensureEmpty()
		fc.emit(OpLoadLocal, int64(condSlot))
		zeroPC := fc.emit(OpJumpIfZero, 0)
		fc.fixups = append(fc.fixups, fixup{pc: zeroPC, target: blk.Succs[1]})
		jumpPC := fc.emit(OpJump, 0)
		fc.fixups = append(fc.fixups, fixup{pc: jumpPC, target: blk.Succs[0]})
		return nil

	case *ssa.Return:
		for _, res := range instr.Results {
			fc.forceToSlot(res)
		}
		fc.ensureEmpty()
		for _, res := range instr.Results {
			fc.emit(OpLoadLocal, int64(fc.slotOf[res]))
		}
		fc.emit(OpReturn, int64(len(instr.Results)))
		return nil

	default:
		return unsupportedInstr(fc.fn, instr, "unsupported terminator")
	}
}

// forceToSlot guarantees that v lives in a frame slot and returns it.
// Constants, which are normally re-materialized on use, are written to a fresh
// slot so the terminator can read them by slot number.
func (fc *funcCompiler) forceToSlot(v ssa.Value) int {
	if slot, ok := fc.slotOf[v]; ok {
		return slot
	}
	slot := fc.assignSlot(v)
	fc.load(v)
	fc.emit(OpStoreLocal, int64(slot))
	fc.consume(1)
	return slot
}

// emitPhiAssignments writes, for every phi in succ, the value contributed by
// the predecessor pred.
func (fc *funcCompiler) emitPhiAssignments(succ, pred *ssa.BasicBlock) {
	predIdx := -1
	for i, p := range succ.Preds {
		if p == pred {
			predIdx = i
			break
		}
	}
	if predIdx < 0 {
		panic("vm: internal error: predecessor not found in successor's list")
	}
	for _, instr := range succ.Instrs {
		phi, ok := instr.(*ssa.Phi)
		if !ok {
			continue
		}
		if predIdx >= len(phi.Edges) {
			panic("vm: internal error: phi has fewer edges than predecessors")
		}
		edge := phi.Edges[predIdx]
		fc.load(edge)
		fc.emit(OpStoreLocal, int64(fc.slotOf[phi]))
		fc.consume(1)
	}
}

// binOpcode selects the instruction for a binary operator.
func binOpcode(op token.Token, x, y NumInfo) (Opcode, error) {
	if x.Type == TypeFloat {
		switch op {
		case token.ADD:
			return OpAddF, nil
		case token.SUB:
			return OpSubF, nil
		case token.MUL:
			return OpMulF, nil
		case token.QUO:
			return OpDivF, nil
		case token.REM:
			return OpRemF, nil
		case token.EQL:
			return OpEqF, nil
		case token.NEQ:
			return OpNeF, nil
		case token.LSS:
			return OpLtF, nil
		case token.LEQ:
			return OpLeF, nil
		case token.GTR:
			return OpGtF, nil
		case token.GEQ:
			return OpGeF, nil
		}
		return 0, fmt.Errorf("unsupported floating point operator %s", op)
	}

	signed := x.Kind == KindInt
	switch op {
	case token.ADD:
		return OpAddI, nil
	case token.SUB:
		return OpSubI, nil
	case token.MUL:
		return OpMulI, nil
	case token.QUO:
		if signed {
			return OpDivI, nil
		}
		return OpDivU, nil
	case token.REM:
		if signed {
			return OpRemI, nil
		}
		return OpRemU, nil
	case token.AND:
		return OpAnd, nil
	case token.OR:
		return OpOr, nil
	case token.XOR:
		return OpXor, nil
	case token.SHL:
		return OpShl, nil
	case token.SHR:
		if signed {
			return OpShr, nil
		}
		return OpShrU, nil
	case token.EQL:
		return OpEqI, nil
	case token.NEQ:
		return OpNeI, nil
	case token.LSS:
		if signed {
			return OpLtI, nil
		}
		return OpLtU, nil
	case token.LEQ:
		if signed {
			return OpLeI, nil
		}
		return OpLeU, nil
	case token.GTR:
		if signed {
			return OpGtI, nil
		}
		return OpGtU, nil
	case token.GEQ:
		if signed {
			return OpGeI, nil
		}
		return OpGeU, nil
	}
	return 0, fmt.Errorf("unsupported integer operator %s", op)
}

// normalizeOperand returns the conversion operand that canonicalizes an integer
// result narrower than 64 bits.
//
// Every integer word is stored in canonical form: zero-extended to 64 bits for
// unsigned types and sign-extended for signed ones. Canonicalizing means
// truncating to the type's width and then extending back to 64 bits, so a
// subsequent 64-bit operation on the word sees the value the type actually
// holds. Without this, a negative int32 result would be stored with zero upper
// bits and interpreted as a large positive value by signed division.
func normalizeOperand(info NumInfo) (int64, bool) {
	if info.Type != TypeInt || info.Bool || info.Bits >= 64 {
		return 0, false
	}
	return MakeConvertOperand(info.Kind, info.Bits, info.Kind, 64), true
}

// constWord renders a constant as a machine word.
func constWord(c *ssa.Const) (uint64, bool) {
	info, ok := NumInfoOf(c.Type())
	if !ok {
		return 0, false
	}
	// Typed nil for a supported numeric/bool type is the zero value.
	if c.Value == nil {
		return 0, true
	}
	switch {
	case info.Bool:
		if constant.BoolVal(c.Value) {
			return 1, true
		}
		return 0, true
	case info.Kind == KindInt:
		v, exact := constant.Int64Val(constant.ToInt(c.Value))
		if !exact {
			return 0, false
		}
		return uint64(v), true
	case info.Kind == KindUint:
		v, exact := constant.Uint64Val(constant.ToInt(c.Value))
		if !exact {
			return 0, false
		}
		return v, true
	case info.Kind == KindF32:
		f, exact := constant.Float32Val(constant.ToFloat(c.Value))
		if !exact {
			return 0, false
		}
		return uint64(math.Float32bits(f)), true
	case info.Kind == KindF64:
		f, exact := constant.Float64Val(constant.ToFloat(c.Value))
		if !exact {
			return 0, false
		}
		return math.Float64bits(f), true
	}
	return 0, false
}

// SortedNativeNames returns the native function names in index order. It is
// used by diagnostics and tests.
func (p *Program) SortedNativeNames() []string {
	names := make([]string, len(p.Natives))
	for i, n := range p.Natives {
		names[i] = n.GoName
	}
	sort.SliceStable(names, func(i, j int) bool { return names[i] < names[j] })
	return names
}

// summary is a compact description of a program, for logs and tests.
func (p *Program) summary() string {
	var sb strings.Builder
	fmt.Fprintf(&sb, "%d virtual function(s), %d native(s), %d byte(s) of bytecode",
		len(p.Funcs), len(p.Natives), p.byteCount())
	return sb.String()
}

func (p *Program) byteCount() int {
	n := 0
	for _, f := range p.Funcs {
		if f != nil {
			n += len(f.Code)
		}
	}
	return n
}
