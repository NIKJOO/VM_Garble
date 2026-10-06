# Garble

**Go symbol and literal obfuscator** with an experimental **stack-based virtualization (VM)** layer for stronger protection against static reverse engineering.

Garble rewrites Go packages at build time: names, literals, and optionally control flow. The VM goes further—selected functions are lowered to a custom bytecode and executed by an embedded interpreter, so the original machine code of those functions never appears in the binary.

> **Status:** Core obfuscation is production-ready. Virtualization is **experimental** and opt-in (`GARBLE_EXPERIMENTAL_VIRTUALIZE=1`).

---

## Table of contents

- [Why garble](#why-garble)
- [Virtualization (VM)](#virtualization-vm)
- [How the VM works](#how-the-vm-works)
- [Supported subset](#supported-subset)
- [Anti-RE hardening](#anti-re-hardening)
- [Control-flow flattening](#control-flow-flattening)
- [Usage](#usage)
- [Build flags](#build-flags)
- [Relationship to control-flow obfuscation](#relationship-to-control-flow-obfuscation)
- [Safety model](#safety-model)
- [Limitations](#limitations)
- [License](#license)

---

## Why garble

A normal `go build` leaves a binary that is easy to inspect:

- Exported and package-level names are readable
- String literals appear in cleartext
- Function bodies compile to ordinary native code

Garble sits in front of the Go toolchain and transforms packages before compilation so that shipped binaries expose far less structure. Virtualization targets the remaining hard problem: **even after names and strings are gone, native code can still be decompiled**. The VM replaces selected functions with bytecode + a dispatcher, so analysts must recover an instruction set, keys, and an interpreter—not just a CFG of x86/ARM.

---

## Virtualization (VM)

### Idea

Virtualization is a compile-time transform:

1. Mark functions with `//garble:virtualize`
2. Garble builds SSA, checks eligibility, and compiles the function to a **fixed-width stack bytecode**
3. The build emits a small **interpreter** (dispatch loop) and **wrappers** that keep the original Go signatures
4. Callers are unchanged; only the implementation is virtualized

When the feature is disabled, the build is byte-for-byte unaffected. When enabled, unsupported functions are left native—never silently miscompiled.

### What the binary contains

For each virtualized function the object file holds roughly:

| Piece | Role |
|-------|------|
| Encoded bytecode | Opaque instruction stream (not native ISA) |
| Dispatcher / interpreter | Decodes and executes the stream |
| Dispatch tables | Used when control-flow flattening is on |
| Wrappers | Same name & signature as the original function |
| Native bridges | Calls from VM code back into ordinary Go |

An analyst recovering the program must treat the dispatcher as a **custom CPU** and the bytecode as a **program for that CPU**.

### Example

```go
//garble:virtualize
func add(a, b int) int {
	return a + b
}

//garble:virtualize
func checksum(data []byte) uint64 { // may be left native if outside the subset
	// ...
}
```

Build:

```bash
GARBLE_EXPERIMENTAL_VIRTUALIZE=1 garble build -o app.exe ./...
```

Only functions that carry the directive **and** pass eligibility analysis are virtualized.

---

## How the VM works

### Value model

Every operand-stack slot is a single **64-bit word**:

- Integers / bools — bit pattern in the word  
- `float64` / `float32` — IEEE-754 bits (float32 in the low 32 bits)  

Pointers, slices, maps, strings, interfaces, and structs are **out of scope** by design so the operand stack stays **invisible to the garbage collector** and cannot be mistaken for a pointer root.

### Instruction set

The machine is a classic stack VM: arithmetic, bitwise ops, compares, branches, local load/store, virtual calls (`OpCallV`), native calls (`OpCallN`), returns, and optional `OpDispatch` for flattened control flow. Instructions are fixed width (`InstrSize = 9`: 1 opcode byte + 8-byte operand).

Execution paths:

- **Interpreter** (`internal/vm`) — tests, equivalence checks, tooling  
- **Emitted Go dispatcher** — what ships in the binary (specialized `switch` / decode loop)

Both paths implement the same semantics; divergence is treated as a bug.

### Pipeline

```text
  //garble:virtualize
           │
           ▼
     SSA + eligibility
           │
           ▼
   bytecode compile ──► verify (stack, types, branches)
           │
           ▼
   optional flatten (dispatch tables)
           │
           ▼
   encode + harden ──► emit wrappers + interpreter
```

---

## Supported subset

Virtualization applies only when **all** of the following hold.

**Supported**

- Package-level functions (no methods, no `init` / `main`)
- Parameters and results: integers, `bool`, `float32`, `float64`
- Non-escaping locals
- Integer / float arithmetic and compares (including float remainder)
- Numeric conversions
- `if` / `for` / `switch` and related control flow
- Direct calls to other virtualized functions (including recursion) or to native functions with word-typed signatures

**Not supported (left native)**

- Methods, closures, generics, variadic functions  
- Interface or indirect calls  
- Builtins (`len`, `make`, `append`, …)  
- Pointers, slices, maps, strings, channels, structs  
- Heap-escaping addresses  

A directive on an unsupported function is a **safe no-op**: the function stays native and the build succeeds.

---

## Anti-RE hardening

On top of basic virtualization, the VM applies a **hardening layer** (see `internal/vm/harden.go`) so the bytecode stream and dispatcher are harder to recover statically.

| Mechanism | Purpose |
|-----------|---------|
| **Polymorphic opcodes** | Logical opcodes are permuted per build seed; wire encoding of e.g. `ADD` differs every build |
| **Position-dependent encoding** | Each instruction is keyed by `(baseKey, pc)` via a strong mixer—not a single global XOR |
| **Separate arg mixing** | Immediates use a different subkey than the opcode byte |
| **Environment-mixed keys** | Host-derived material is mixed into keys so a static key dump is incomplete |
| **Multi-layer dispatch tables** | Table entries use independent keys (not the code key alone) |
| **Integrity checksum** | Interpreter and emitted runtime refuse to run if code bytes were patched |
| **Hash-chained block metadata** | Per-PC chain hashes recorded at compile time |
| **Handler order shuffle** | Emitted `switch` case order is seed-permuted |
| **Handler duplication** | Alternate wire encodings / duplicate cases map to the same handler |
| **Junk / decoy cases** | Unreachable switch arms with opaque predicates |
| **Opaque predicates** | Always-true / always-false guards inside the dispatch loop |
| **Scrambled dispatcher CFG** | Lightweight state-machine step around fetch/decode |
| **Instruction splitting** | e.g. constants materialised as `(c^k) XOR k` |
| **Decoy native bridges** | Never-called stubs present in native tables |
| **Nested virtualization (`OpNested`)** | Secondary bytecode blobs under a separate nested key |
| **Control-flow flattening** | Indirect branches through keyed tables (see below) |

**Explicitly not implemented:** anti-debugging (debugger detection / intentional behavioral change under debug).

Hardening is deterministic for a fixed seed so builds remain reproducible when `-seed` is fixed.

---

## Control-flow flattening

Virtualization alone still leaves a readable bytecode CFG (direct jumps). Flattening rewrites that CFG:

1. Split bytecode into basic blocks  
2. Replace edges with **push state + `DISPATCH`** through a per-function table  
3. Permute block order and state numbering independently  
4. Pad tables with decoy targets  

Optional **decoy edges** insert always-holding predicates and dead branches so every dispatch looks data-dependent.

Flattening runs as a post-pass: it does not change eligibility. It is on by default when virtualization runs; disable with `GARBLE_EXPERIMENTAL_VMFLATTEN=0`, or enable full decoys with `GARBLE_EXPERIMENTAL_VMFLATTEN=decoys`.

---

## Usage

### Basic obfuscation (no VM)

```bash
garble build -o app.exe ./...
```

### With virtualization

```bash
GARBLE_EXPERIMENTAL_VIRTUALIZE=1 garble build -o app.exe ./...
```

### Typical hardened release build

```bash
GARBLE_EXPERIMENTAL_VIRTUALIZE=1 \
  garble -literals -tiny -seed=random \
  build -trimpath -ldflags="-s -w" -o app.exe ./...
```

| Flag | Effect |
|------|--------|
| `-literals` | Obfuscate string literals |
| `-tiny` | Smaller binary, stripped-down runtime extras |
| `-seed=random` | New polymorphism per build |
| `-trimpath` | Strip filesystem paths |
| `-ldflags="-s -w"` | Strip symbol table and DWARF |

Full Sample Command 

` garble -literals -tiny -seed=random build -trimpath -ldflags="-s -w" -o YourAppname.exe `

### Marking functions

```go
//garble:virtualize
func sensitive(x, y int) int {
	return x*y + x
}
```

Prefer small, hot, pure numeric helpers. Keep I/O, reflection, and complex types in native functions and call them through native bridges when needed.

---

## Build flags

Environment variables related to the VM:

| Variable | Meaning |
|----------|---------|
| `GARBLE_EXPERIMENTAL_VIRTUALIZE=1` | Enable virtualization |
| `GARBLE_EXPERIMENTAL_VMFLATTEN=0` | Disable flattening |
| `GARBLE_EXPERIMENTAL_VMFLATTEN=decoys` | Flatten + opaque decoy edges |

Garble’s usual flags (`-literals`, `-tiny`, `-seed`, …) apply independently of the VM.

---

## Relationship to control-flow obfuscation

Garble also offers **source-level** control-flow obfuscation (`//garble:controlflow`, `GARBLE_EXPERIMENTAL_CONTROLFLOW`). The two layers compose:

- **Control flow** rewrites Go source so the **native** code is harder to follow  
- **Virtualization + flatten** rewrite **bytecode** so the **VM’s** CFG is harder to recover  

They can be enabled together; functions tagged for only one transform are unaffected by the other.

---

## Safety model

- Eligibility is checked **before** any mutation  
- Compile/verify failures are **hard errors**, not silent fallbacks mid-function  
- Unsupported constructs → function left **100% native**  
- Feature off → **no** change to the build artifact  
- Interpreter and emitted dispatcher are tested for semantic equivalence  

The VM prioritizes **correctness and GC safety** over supporting the entire Go language.

---

## Limitations

- Experimental; API and encoding may change  
- Performance cost is real (interpreted bytecode vs native)—use on sensitive paths, not everything  
- Large surface of Go (methods, generics, containers, interfaces) remains native by design  
- Not a substitute for server-side controls, attestation, or proper secret handling  
- Determined analysts with a debugger can still observe behavior; hardening raises static cost, it does not make reverse engineering impossible  



## License

GNU General Public License v3.0
