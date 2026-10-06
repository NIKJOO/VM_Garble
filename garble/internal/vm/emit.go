package vm

import (
	"fmt"
	"go/format"
	"sort"
	"strings"
)

// EmitterOptions controls how a Program is rendered as Go source.
type EmitterOptions struct {
	// Prefix is prepended to every generated top-level identifier. It must be a
	// valid Go identifier prefix and should be unique within the package.
	Prefix string
	// PackageName is the package clause of the generated file.
	PackageName string
	// Imports maps an import path to the local name the generated file should
	// use for it. It names the packages the native bridges and wrappers refer to;
	// the caller is responsible for adding those imports to the build. The
	// runtime itself needs only unsafe, which the emitter adds automatically.
	Imports map[string]string
}

// DefaultEmitterOptions returns options with the conventional garble prefix.
func DefaultEmitterOptions() EmitterOptions {
	return EmitterOptions{Prefix: "_vmp_"}
}

// opBodies maps each opcode to the body of its case in the emitted dispatcher.
//
// The dispatcher is a real interpreter: it decodes one virtual instruction at a
// time from the (key-obfuscated) bytecode and executes it against a word-level
// operand stack. Keeping the bodies here, next to the opcode enumeration, makes
// it obvious which instruction each case implements; the reference interpreter
// in exec.go must agree with them, which TestInterpreterMatchesEmitted checks
// by compiling and running generated programs.
//
// The following locals are available in every body:
//
//	code, key  the program's encoded functions and decode key
//	stack      the operand stack, []uint64, last element on top
//	locals     the current frame's slots, []uint64
//	frames     the saved frames, []_vmpFrame
//	cur        the index of the running virtual function
//	pc, nextPC the current and next instruction offsets
//	popN       func(int) []uint64, removes n words from the top
//	natives    the native bridge table, []func([]uint64) []uint64
var opBodies = map[Opcode]string{
	OpNop: ``,
	OpConst: `
			stack = append(stack, uint64(arg))`,
	OpConstF: `
			stack = append(stack, uint64(arg))`,
	OpPop: `
			popN(1)`,
	OpDup: `
			stack = append(stack, stack[len(stack)-1])`,
	OpSwap: `
			n := len(stack)
			stack[n-1], stack[n-2] = stack[n-2], stack[n-1]`,
	OpLoadLocal: `
			stack = append(stack, locals[arg])`,
	OpStoreLocal: `
			locals[arg] = popN(1)[0]`,

	OpAddI: intBinBody("a + b"),
	OpSubI: intBinBody("a - b"),
	OpMulI: intBinBody("a * b"),
	OpDivI: intBinBody("uint64(int64(a) / int64(b))"),
	OpRemI: intBinBody("uint64(int64(a) % int64(b))"),
	OpDivU: intBinBody("a / b"),
	OpRemU: intBinBody("a % b"),
	OpAnd:  intBinBody("a & b"),
	OpOr:   intBinBody("a | b"),
	OpXor:  intBinBody("a ^ b"),
	OpShl:  intBinBody("a << b"),
	OpShr:  intBinBody("uint64(int64(a) >> b)"),
	OpShrU: intBinBody("a >> b"),
	OpNegI: intUnBody("-a"),
	OpNot:  intUnBody("^a"),

	OpAddF: floatBinBody("x + y"),
	OpSubF: floatBinBody("x - y"),
	OpMulF: floatBinBody("x * y"),
	OpDivF: floatBinBody("x / y"),
	OpRemF: floatBinBody("_vmpMod(x, y)"),
	OpNegF: `
			n := len(stack)
			stack[n-1] = _vmpF64bits(-_vmpF64frombits(stack[n-1]))`,

	OpEqI: intCmpBody("a == b"),
	OpNeI: intCmpBody("a != b"),
	OpLtI: intCmpBody("int64(a) < int64(b)"),
	OpLeI: intCmpBody("int64(a) <= int64(b)"),
	OpGtI: intCmpBody("int64(a) > int64(b)"),
	OpGeI: intCmpBody("int64(a) >= int64(b)"),
	OpLtU: intCmpBody("a < b"),
	OpLeU: intCmpBody("a <= b"),
	OpGtU: intCmpBody("a > b"),
	OpGeU: intCmpBody("a >= b"),

	OpEqF: floatCmpBody("x == y"),
	OpNeF: floatCmpBody("x != y"),
	OpLtF: floatCmpBody("x < y"),
	OpLeF: floatCmpBody("x <= y"),
	OpGtF: floatCmpBody("x > y"),
	OpGeF: floatCmpBody("x >= y"),

	OpNotB: `
			stack[len(stack)-1] = 1 - stack[len(stack)-1]`,
	OpConvert: `
			stack[len(stack)-1] = conv(stack[len(stack)-1], arg)`,

	OpJump: `
			nextPC = int(arg)`,
	OpJumpIfZero: `
			if popN(1)[0] == 0 {
				nextPC = int(arg)
			}`,
	OpJumpIfNotZero: `
			if popN(1)[0] != 0 {
				nextPC = int(arg)
			}`,

	OpDispatch: `
			n := len(stack)
			st := stack[n-1]
			stack = stack[:n-1]
			nextPC = int(uint64(dispOf[cur][st]) ^ _vmpTableKey ^ _vmpTableKey2 ^ _vmpMix64(_vmpTableKey) ^ _vmpMix64(_vmpTableKey2))`,

	OpCallV: `
			callee := int(arg)
			argv := popN(paramsOf[callee])
			frames = append(frames, _vmpFrame{fn: cur, locals: locals, retPC: nextPC})
			cur = callee
			locals = make([]uint64, localsOf[callee])
			copy(locals, argv)
			nextPC = 0`,
	OpCallN: `
			arity := len(nativeArity[arg])
			res := natives[arg](stack[len(stack)-arity:])
			stack = stack[:len(stack)-arity]
			stack = append(stack, res...)`,

	OpReturn: `
			if len(frames) == 0 {
				return append([]uint64(nil), stack[len(stack)-int(arg):]...)
			}
			res := popN(int(arg))
			f := frames[len(frames)-1]
			frames = frames[:len(frames)-1]
			cur = f.fn
			locals = f.locals
			nextPC = f.retPC
			stack = append(stack, res...)`,
	OpNested: `
			_ = _vmpNested
			_ = arg`,
	OpHalt: `
			return append([]uint64(nil), stack...)`,
}

func intBinBody(expr string) string {
	return `
			n := len(stack)
			a, b := stack[n-2], stack[n-1]
			stack = stack[:n-1]
			stack[n-2] = ` + expr
}

func intUnBody(expr string) string {
	return `
			n := len(stack)
			a := stack[n-1]
			stack[n-1] = ` + expr
}

func floatBinBody(expr string) string {
	return `
			n := len(stack)
			x, y := _vmpF64frombits(stack[n-2]), _vmpF64frombits(stack[n-1])
			stack = stack[:n-1]
			stack[n-2] = _vmpF64bits(` + expr + `)`
}

func intCmpBody(expr string) string {
	return `
			n := len(stack)
			a, b := stack[n-2], stack[n-1]
			stack = stack[:n-1]
			if ` + expr + ` {
				stack[n-2] = 1
			} else {
				stack[n-2] = 0
			}`
}

func floatCmpBody(expr string) string {
	return `
			n := len(stack)
			x, y := _vmpF64frombits(stack[n-2]), _vmpF64frombits(stack[n-1])
			stack = stack[:n-1]
			if ` + expr + ` {
				stack[n-2] = 1
			} else {
				stack[n-2] = 0
			}`
}

// runtimePrelude is the fixed part of the emitted runtime, before the
// dispatcher's switch statement.
const runtimePreludeTemplate = `
type _vmpFrame struct {
	fn     int
	locals []uint64
	retPC  int
}

// _vmpRun executes virtual function fn with the given argument words.
//
// This is a real bytecode interpreter: it decodes one virtual instruction at a
// time from the key-obfuscated code and executes it against a word-level
// operand stack. Nothing here resembles the original source function.
func _vmpRun(fn int, args []uint64) []uint64 {
	// Arguments are delivered through the frame, not through the operand stack.
	stack := make([]uint64, 0, 32)
	locals := make([]uint64, _vmpLocals[fn])
	copy(locals, args)
	var frames []_vmpFrame
	cur := fn
	pc := 0
	popN := func(n int) []uint64 {
		out := stack[len(stack)-n:]
		stack = stack[:len(stack)-n]
		return out
	}
	// Aliases bound once per call keep the dispatch bodies compact. They are
	// constant for the duration of the call.
	codeAll := _vmpCode
	baseKey := _vmpKey
	natives := _vmpNatives
	nativeArity := _vmpNativeArity
	localsOf := _vmpLocals
	paramsOf := _vmpParams
	dispOf := _vmpDispatch
	conv := _vmpConv
	opDec := _vmpOpDec
	// Integrity: refuse to run if code was patched.
	if _vmpIntegrity != 0 && _vmpChecksum(codeAll) != _vmpIntegrity {
		panic("vmp: integrity check failed")
	}
	// Opaque always-true guard (keeps dead-looking path in the binary).
	_ = _vmpOpaqueTrue(baseKey)
	dispState := baseKey
	for {
		// Scrambled dispatcher CFG: state machine step before each fetch.
		dispState = _vmpMix64(dispState ^ uint64(pc) ^ baseKey)
		if _vmpOpaqueFalse(dispState) {
			dispState ^= 1
		}
		code := codeAll[cur]
		// Position-dependent subkey (splitmix-style), independent of rolling state
		// so branches remain valid.
		// Match vm.effectiveKey(baseKey, envKey, 0, pc):
		// mix64(posKey(base^env, pc)) with posKey = mix64(base^pc*const^(pc<<17))
		base := baseKey ^ _vmpEnvKey
		pk := base ^ uint64(pc)*0x9e3779b97f4a7c15 ^ (uint64(pc) << 17)
		pk = _vmpMix64(pk)
		pk = _vmpMix64(pk)
		wire := code[pc] ^ byte(pk) ^ byte(pk>>8) ^ byte(pk>>16)
		op := opDec[wire]
		argKey := _vmpMix64(pk ^ 0xD6E8FEB86659FD93)
		arg := int64(_vmpRead64(code[pc+1:]) ^ argKey)
		nextPC := pc + %[1]d
		// Decoy opaque branch never taken; confuses static CFG recovery of the dispatcher.
		if _vmpOpaqueFalse(uint64(pc) ^ baseKey) {
			nextPC = 0
		}
		switch op {
%[2]s
		default:
			panic("vmp: unknown instruction")
		}
		pc = nextPC
	}
}

// _vmpBoolToWord and _vmpWordToBool are the canonical boolean conversions used
// by generated wrappers. Booleans travel as the words 0 and 1.
func _vmpBoolToWord(b bool) uint64 {
	if b {
		return 1
	}
	return 0
}

func _vmpWordToBool(w uint64) bool { return w != 0 }

func _vmpMix64(z uint64) uint64 {
	z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9
	z = (z ^ (z >> 27)) * 0x94d049bb133111eb
	return z ^ (z >> 31)
}

func _vmpOpaqueTrue(x uint64) bool  { return (x*(x+1))&1 == 0 }
func _vmpOpaqueFalse(x uint64) bool { return (x*(x+1))&1 == 1 }

func _vmpChecksum(codeAll [][]byte) uint64 {
	h := _vmpKey ^ _vmpEnvKey
	for i, code := range codeAll {
		for j := 0; j+8 <= len(code); j += 8 {
			v := _vmpRead64(code[j:])
			h = _vmpMix64(h ^ v ^ uint64(j) ^ uint64(i)<<32)
		}
		for j := len(code) - len(code)%%8; j < len(code); j++ {
			h = _vmpMix64(h ^ uint64(code[j]) ^ uint64(j)<<8)
		}
	}
	return h
}

// _vmpRead64 decodes a little-endian uint64 without importing encoding/binary.
func _vmpRead64(b []byte) uint64 {
	return uint64(b[0]) | uint64(b[1])<<8 | uint64(b[2])<<16 | uint64(b[3])<<24 |
		uint64(b[4])<<32 | uint64(b[5])<<40 | uint64(b[6])<<48 | uint64(b[7])<<56
}

// Float bit conversions. The generated file must not depend on the math package,
// because a package that never used math cannot import it in this build; unsafe
// is treated specially by the compiler and can always be imported.
func _vmpF64bits(f float64) uint64         { return *(*uint64)(unsafe.Pointer(&f)) }
func _vmpF64frombits(b uint64) float64      { return *(*float64)(unsafe.Pointer(&b)) }
func _vmpF32bits(f float32) uint32          { return *(*uint32)(unsafe.Pointer(&f)) }
func _vmpF32frombits(b uint32) float32      { return *(*float32)(unsafe.Pointer(&b)) }

// _vmpMod implements floating-point remainder without importing math.
// Matches math.Mod for finite non-zero y: result has the sign of x and
// magnitude less than |y|.
func _vmpMod(x, y float64) float64 {
	if y == 0 {
		return _vmpF64frombits(0x7ff8000000000001) // NaN
	}
	r := x - y*float64(int64(x/y))
	// Correct residual toward zero for negative quotients that truncated away from zero.
	if (x < 0) != (r < 0) && r != 0 {
		if y < 0 {
			r -= y
		} else {
			r += y
		}
	}
	return r
}

// _vmpConv applies a numeric conversion to a word. It mirrors vm.Convert.
func _vmpConv(v uint64, operand int64) uint64 {
	fromKind := uint32(operand) & 0xff
	fromBits := (uint32(operand) >> 8) & 0xff
	toKind := (uint32(operand) >> 16) & 0xff
	toBits := (uint32(operand) >> 24) & 0xff
	_ = fromBits
	_ = toBits
	signExtend := func(v uint64, bits uint32) int64 {
		shift := uint(64 - bits)
		return int64(v<<shift) >> shift
	}
	zeroExtend := func(v uint64, bits uint32) uint64 {
		return v & (1<<bits - 1)
	}
	switch toKind {
	case %[3]d, %[4]d:
		var i int64
		switch fromKind {
		case %[3]d:
			i = signExtend(v, fromBits)
		case %[4]d:
			i = int64(zeroExtend(v, fromBits))
		case %[5]d:
			i = int64(_vmpF64frombits(v))
		case %[6]d:
			i = int64(_vmpF32frombits(uint32(v)))
		}
		if toKind == %[4]d {
			return zeroExtend(uint64(i), toBits)
		}
		return uint64(signExtend(uint64(i), toBits))
	case %[5]d:
		var f float64
		switch fromKind {
		case %[3]d:
			f = float64(signExtend(v, fromBits))
		case %[4]d:
			f = float64(zeroExtend(v, fromBits))
		case %[5]d:
			f = _vmpF64frombits(v)
		case %[6]d:
			f = float64(_vmpF32frombits(uint32(v)))
		}
		return _vmpF64bits(f)
	case %[6]d:
		var f float32
		switch fromKind {
		case %[3]d:
			f = float32(signExtend(v, fromBits))
		case %[4]d:
			f = float32(zeroExtend(v, fromBits))
		case %[5]d:
			f = float32(_vmpF64frombits(v))
		case %[6]d:
			f = _vmpF32frombits(uint32(v))
		}
		return uint64(_vmpF32bits(f))
	}
	panic("vmp: bad conversion")
}
`

// Emit renders the program's runtime support as a complete Go file.
//
// The file contains the runtime declarations only; callers that also need the
// per-function wrappers should use EmitPackage.
func (p *Program) Emit(opts EmitterOptions) ([]byte, error) {
	decls, err := p.emitDecls(opts)
	if err != nil {
		return nil, err
	}
	return p.assembleFile(opts, decls, "")
}

// emitDecls builds the runtime declarations of the program.
func (p *Program) emitDecls(opts EmitterOptions) (string, error) {
	if opts.Prefix == "" {
		return "", fmt.Errorf("vm: emitter prefix must not be empty")
	}
	if err := p.Verify(); err != nil {
		return "", err
	}

	var sb strings.Builder

	// Program key and hardening metadata.
	fmt.Fprintf(&sb, "\n// Code decode key.\nvar %skey uint64 = %#x\n", opts.Prefix, p.Key)
	tableKey := p.Key
	integrity := uint64(0)
	if p.Hardening != nil {
		tableKey = p.Hardening.TableKey
		p.ComputeIntegrity()
		integrity = p.Hardening.Integrity
	}
	fmt.Fprintf(&sb, "\nvar %stableKey uint64 = %#x\n", opts.Prefix, tableKey)
	tableKey2 := tableKey
	envKey := uint64(0)
	workFactor := uint64(0)
	if p.Hardening != nil {
		tableKey2 = p.Hardening.TableKey2
		envKey = p.Hardening.EnvKey
		workFactor = p.Hardening.WorkFactor
	}
	fmt.Fprintf(&sb, "\nvar %stableKey2 uint64 = %#x\n", opts.Prefix, tableKey2)
	fmt.Fprintf(&sb, "\nvar %senvKey uint64 = %#x\n", opts.Prefix, envKey)
	fmt.Fprintf(&sb, "\nvar %sworkFactor uint64 = %#x\n", opts.Prefix, workFactor)
	fmt.Fprintf(&sb, "\nvar %sintegrity uint64 = %#x\n", opts.Prefix, integrity)
	// Polymorphic opcode decode table (wire byte -> logical opcode).
	fmt.Fprintf(&sb, "\nvar %sopDec = [256]byte{\n\t", opts.Prefix)
	for i := 0; i < 256; i++ {
		v := byte(i)
		if p.Hardening != nil {
			v = byte(p.Hardening.Dec[i])
		}
		if i > 0 && i%16 == 0 {
			sb.WriteString("\n\t")
		}
		fmt.Fprintf(&sb, "%#02x, ", v)
	}
	sb.WriteString("\n}\n")

	// Encoded code, one byte slice per virtual function.
	fmt.Fprintf(&sb, "\nvar %scode = [][]byte{\n", opts.Prefix)
	for _, f := range p.Funcs {
		sb.WriteString("\t{")
		for i, b := range f.Code {
			if i > 0 {
				sb.WriteString(", ")
			}
			fmt.Fprintf(&sb, "%#02x", b)
		}
		sb.WriteString("},\n")
	}
	sb.WriteString("}\n")

	// Nested virtualization blobs.
	fmt.Fprintf(&sb, "\nvar %snested = [][]byte{\n", opts.Prefix)
	for _, blob := range p.Nested {
		sb.WriteString("\t{")
		for i, b := range blob {
			if i > 0 {
				sb.WriteString(", ")
			}
			fmt.Fprintf(&sb, "%#02x", b)
		}
		sb.WriteString("},\n")
	}
	sb.WriteString("}\n")

	// Dispatch tables for control-flow flattened functions. Each entry is the
	// byte offset of a block, stored XORed with the program key so that the
	// table does not read as a list of offsets. A function that is not flattened
	// has an empty table and no OpDispatch instruction.
	fmt.Fprintf(&sb, "\nvar %sdispatch = [][]int64{\n", opts.Prefix)
	for _, f := range p.Funcs {
		sb.WriteString("\t{")
		for i, target := range f.Dispatch {
			if i > 0 {
				sb.WriteString(", ")
			}
			tk, tk2 := p.Key, p.Key
			if p.Hardening != nil {
				tk, tk2 = p.Hardening.TableKey, p.Hardening.TableKey2
			}
			fmt.Fprintf(&sb, "%d", encodeDispatchAffine(int(target), tk, tk2))
		}
		sb.WriteString("},\n")
	}
	sb.WriteString("}\n")

	// Frame sizes.
	fmt.Fprintf(&sb, "\nvar %slocals = []int{", opts.Prefix)
	for i, f := range p.Funcs {
		if i > 0 {
			sb.WriteString(", ")
		}
		fmt.Fprint(&sb, f.NumLocals)
	}
	sb.WriteString("}\n")

	// Parameter counts, used to slice the operand stack before a virtual call.
	// The caller pushes only the arguments, but the callee's frame also holds
	// its local variables, so the two counts differ.
	fmt.Fprintf(&sb, "\nvar %sparams = []int{", opts.Prefix)
	for i, f := range p.Funcs {
		if i > 0 {
			sb.WriteString(", ")
		}
		fmt.Fprint(&sb, len(f.Params))
	}
	sb.WriteString("}\n")

	// Native arity, used to slice the operand stack before a native call.
	fmt.Fprintf(&sb, "\nvar %snativeArity = [][]int{\n", opts.Prefix)
	for _, n := range p.Natives {
		sb.WriteString("\t{")
		for i, t := range n.Params {
			if i > 0 {
				sb.WriteString(", ")
			}
			fmt.Fprint(&sb, int(t))
		}
		sb.WriteString("},\n")
	}
	sb.WriteString("}\n")

	// Native bridges. Each bridge converts words to the real function's
	// parameter types, calls it, and converts the results back to words. The
	// body is rendered by the SSA compiler, which knows the real types and the
	// import aliases the generated file uses.
	fmt.Fprintf(&sb, "\nvar %snatives = []func([]uint64) []uint64{\n", opts.Prefix)
	allNatives := append([]*NativeFunc{}, p.Natives...)
	allNatives = append(allNatives, p.DecoyNatives...)
	for i, n := range allNatives {
		if n.Bridge == "" {
			return "", fmt.Errorf("vm: native %d (%s) has no bridge body", i, n.GoName)
		}
		sb.WriteString("\tfunc(a []uint64) []uint64 { " + n.Bridge + " },\n")
	}
	sb.WriteString("}\n")

	// The dispatcher. Case order is permuted when hardening is active so the
	// physical layout of handlers differs across builds.
	var cases strings.Builder
	order := make([]Opcode, 0, int(opCount))
	if p.Hardening != nil && len(p.Hardening.HandlerOrder) > 0 {
		order = append(order, p.Hardening.HandlerOrder...)
	} else {
		for op := Opcode(0); op < opCount; op++ {
			order = append(order, op)
		}
	}
	for _, op := range order {
		body, ok := opBodies[op]
		if !ok {
			continue
		}
		// Primary handler under logical opcode number (after polymorphic map,
		// the runtime switch still keys on decoded logical op).
		fmt.Fprintf(&cases, "\t\tcase %d: // %s\n%s\n", int(op), op, body)
		// Handler duplication: extra cases that execute the same body.
		if p.Hardening != nil {
			for _, wire := range p.Hardening.HandlerDup[op] {
				fmt.Fprintf(&cases, "\t\tcase %d: // dup %s\n%s\n", int(wire), op, body)
			}
		}
	}
	// Anti-disassembly / decoy cases: unreachable junk that never matches a
	// real decoded opcode under the current Dec table, but appears in the binary.
	if p.Hardening != nil {
		junkSeed := p.Hardening.JunkSeed
		for i := 0; i < 8; i++ {
			junkSeed = mix64(junkSeed + uint64(i))
			caseNum := 200 + int(junkSeed%40)
			fmt.Fprintf(&cases, "\t\tcase %d: // junk\n\t\t\t_ = _vmpOpaqueFalse(uint64(%d))\n\t\t\tnextPC = nextPC\n", caseNum, caseNum)
		}
	}

	prelude := fmt.Sprintf(runtimePreludeTemplate,
		InstrSize,
		strings.TrimRight(cases.String(), "\n"),
		KindInt, KindUint, KindF64, KindF32,
	)
	// Bind the shared identifiers to the generated names. Order matters: the
	// longer names are listed first so that a shorter name cannot match inside a
	// longer one ("_vmpConv" must not be rewritten as "_vmp_conv" twice).
	prelude = strings.NewReplacer(
		"_vmpF64frombits", opts.Prefix+"F64frombits",
		"_vmpF32frombits", opts.Prefix+"F32frombits",
		"_vmpMod", opts.Prefix+"Mod",
		"_vmpNativeArity", opts.Prefix+"nativeArity",
		"_vmpF64bits", opts.Prefix+"F64bits",
		"_vmpF32bits", opts.Prefix+"F32bits",
		"_vmpRead64", opts.Prefix+"Read64",
		"_vmpNatives", opts.Prefix+"natives",
		"_vmpBoolToWord", opts.Prefix+"BoolToWord",
		"_vmpWordToBool", opts.Prefix+"WordToBool",
		"_vmpLocals", opts.Prefix+"locals",
		"_vmpParams", opts.Prefix+"params",
		"_vmpDispatch", opts.Prefix+"dispatch",
		"_vmpFrame", opts.Prefix+"Frame",
		"_vmpCode", opts.Prefix+"code",
		"_vmpConv", opts.Prefix+"conv",
		"_vmpRun", opts.Prefix+"Run",
		"_vmpKey", opts.Prefix+"key",
		"_vmpTableKey", opts.Prefix+"tableKey",
		"_vmpIntegrity", opts.Prefix+"integrity",
		"_vmpOpDec", opts.Prefix+"opDec",
		"_vmpChecksum", opts.Prefix+"checksum",
		"_vmpOpaqueTrue", opts.Prefix+"opaqueTrue",
		"_vmpOpaqueFalse", opts.Prefix+"opaqueFalse",
		"_vmpMix64", opts.Prefix+"mix64",
		"_vmpTableKey2", opts.Prefix+"tableKey2",
		"_vmpEnvKey", opts.Prefix+"envKey",
		"_vmpWorkFactor", opts.Prefix+"workFactor",
		"_vmpNested", opts.Prefix+"nested",
	).Replace(prelude)
	sb.WriteString(prelude)

	return sb.String(), nil
}

// assembleFile prepends the package clause and imports to decls and formats the
// result. extra is appended after decls, for generated wrapper functions.
//
// The runtime always references unsafe, which is imported unconditionally;
// opts.Imports supplies the imports the native bridges or wrappers need.
func (p *Program) assembleFile(opts EmitterOptions, decls, extra string) ([]byte, error) {
	imports := map[string]string{}
	for path, alias := range opts.Imports {
		imports[path] = alias
	}
	// The runtime always uses unsafe for float bit conversions. unsafe is
	// handled specially by the compiler and import resolution, so it can always
	// be referenced even when the surrounding package never imported it.
	if imports["unsafe"] == "" {
		imports["unsafe"] = "unsafe"
	}
	paths := make([]string, 0, len(imports))
	for path := range imports {
		paths = append(paths, path)
	}
	sort.Strings(paths)

	var sb strings.Builder
	sb.WriteString("package " + opts.PackageName + "\n\nimport (\n")
	for _, path := range paths {
		fmt.Fprintf(&sb, "\t%s %q\n", imports[path], path)
	}
	sb.WriteString(")\n")
	sb.WriteString(decls)
	sb.WriteString(extra)

	out, err := format.Source([]byte(sb.String()))
	if err != nil {
		return nil, fmt.Errorf("vm: generated source does not parse: %w", err)
	}
	return out, nil
}

// opCount is one past the last defined opcode.
const opCount = OpHalt + 1
