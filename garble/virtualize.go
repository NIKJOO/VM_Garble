package main

import (
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"log"
	mathrand "math/rand"
	"strconv"
	"strings"

	"golang.org/x/tools/go/ast/astutil"
	"golang.org/x/tools/go/ssa"
	ah "mvdan.cc/garble/internal/asthelper"
	"mvdan.cc/garble/internal/vm"
)

const (
	// virtualizeFileName is the generated file that holds the virtual machine
	// runtime and the wrappers that replace the original function bodies.
	virtualizeFileName = "GARBLE_virtualize.go"
	// virtualizeDirectiveName marks a function to be virtualized.
	virtualizeDirectiveName = "//garble:virtualize"
	// virtualizeImportPrefix names the imports the generated file needs.
	virtualizeImportPrefix = "___garble_import"
)

// virtualizeImporter resolves a package for the typecheck that follows
// virtualization. The generated file always needs encoding/binary and math,
// which the package being compiled may not import, so a miss falls back to the
// default importer and resolves the package from GOROOT.
//
// The paths that hit the fallback are also collected into the import config by
// the caller, so the subsequent real compile resolves them from the build cache
// like any other dependency.
type virtualizeImporter struct {
	base importerWithMap
}

func (im virtualizeImporter) Import(path string) (*types.Package, error) {
	return im.ImportFrom(path, "", 0)
}

func (im virtualizeImporter) ImportFrom(path, dir string, mode types.ImportMode) (*types.Package, error) {
	pkg, err := im.base.ImportFrom(path, dir, mode)
	if err == nil {
		return pkg, nil
	}
	return importer.Default().Import(path)
}

// virtualize replaces the bodies of every function carrying a
// //garble:virtualize directive with a call into a stack-based virtual machine.
//
// The transformation is all-or-nothing per function: functions outside the
// supported subset (see the vm package's eligibility checks) are left exactly
// as they were, so a program with no eligible functions is unchanged. Original
// declarations are blanked and re-emitted as wrappers in a new file so that
// every existing caller keeps its exact name and signature.
func virtualize(fset *token.FileSet, ssaPkg *ssa.Package, files []*ast.File, obfRand *mathrand.Rand) (newFileName string, newFile *ast.File, affectedFiles []*ast.File, err error) {
	type candidate struct {
		fn   *ssa.Function
		decl *ast.FuncDecl
	}

	var candidates []candidate
	for _, file := range files {
		affected := false
		for _, decl := range file.Decls {
			funcDecl, ok := decl.(*ast.FuncDecl)
			if !ok || funcDecl.Doc == nil {
				continue
			}
			hasDirective := false
			for _, comment := range funcDecl.Doc.List {
				if strings.TrimSpace(comment.Text) == virtualizeDirectiveName {
					hasDirective = true
					break
				}
			}
			if !hasDirective {
				continue
			}

			path, _ := astutil.PathEnclosingInterval(file, funcDecl.Pos(), funcDecl.Pos())
			ssaFunc := ssa.EnclosingFunction(ssaPkg, path)
			if ssaFunc == nil {
				panic("function exists in ast but not found in ssa")
			}
			candidates = append(candidates, candidate{fn: ssaFunc, decl: funcDecl})
			affected = true
		}
		if affected {
			affectedFiles = append(affectedFiles, file)
		}
	}
	if len(candidates) == 0 {
		return
	}

	// The generated file refers to imported packages through aliases recorded
	// here; the aliases become the file's imports.
	imports := make(map[string]string)
	importName := func(pkg *types.Package) string {
		if pkg == nil || pkg.Path() == ssaPkg.Pkg.Path() {
			return ""
		}
		name, ok := imports[pkg.Path()]
		if !ok {
			name = virtualizeImportPrefix + strconv.Itoa(len(imports))
			imports[pkg.Path()] = name
		}
		return name
	}

	// The decode key is derived from the same deterministic rand the rest of
	// garble uses, so two builds with the same seed produce the same output.
	opts := vm.DefaultEmitterOptions()
	opts.PackageName = files[0].Name.Name

	key := obfRand.Uint64()
	comp := vm.NewCompiler(key, importName)
	comp.SetPrefix(opts.Prefix)

	// Eligibility is checked for every candidate before anything is registered,
	// so the decision to virtualize one function never depends on another.
	var eligible []candidate
	for _, c := range candidates {
		if err := comp.Eligible(c.fn); err != nil {
			log.Printf("not virtualizing %s: %v", c.fn, err)
			continue
		}
		eligible = append(eligible, c)
	}
	if len(eligible) == 0 {
		return
	}

	// Register all functions before compiling any, so that calls between
	// virtualized functions resolve to OpCallV instead of a native bridge.
	for _, c := range eligible {
		comp.Add(c.fn)
	}
	for _, c := range eligible {
		if _, err := comp.Compile(c.fn); err != nil {
			return "", nil, nil, fmt.Errorf("virtualizing %s: %w", c.fn, err)
		}
		log.Printf("virtualized %s", c.fn)
	}

	// Flattening runs after every function is compiled, so that it can never
	// influence which functions are eligible or how calls between them are
	// encoded. It rewrites each function's control flow into an indirect
	// dispatch through an obfuscated state table.
	prog := comp.Program()
	if flagVMFlatten {
		flattenOpts := vm.DefaultFlattenOptions(prog.Key)
		flattenOpts.DecoyEdges = flagVMDecoys
		if err := prog.Flatten(flattenOpts); err != nil {
			return "", nil, nil, fmt.Errorf("flattening virtualized control flow: %w", err)
		}
		log.Printf("flattened control flow of %d virtualized function(s)", len(prog.Funcs))
	}

	registered := comp.Funcs()
	genFuncs := make([]vm.GenFunc, 0, len(registered))
	for i, fn := range registered {
		genFuncs = append(genFuncs, vm.GenFunc{
			Name:      fn.Name(),
			Sig:       fn.Signature,
			Index:     i,
			Qualifier: importName,
		})
	}

	opts.Imports = imports
	src, err := prog.EmitPackage(opts, genFuncs)
	if err != nil {
		return "", nil, nil, err
	}

	newFile, err = parser.ParseFile(fset, virtualizeFileName, src, parser.ParseComments)
	if err != nil {
		return "", nil, nil, fmt.Errorf("parsing generated virtualization file: %w", err)
	}

	// Only now that every wrapper is known to be valid do the original
	// declarations get blanked.
	for _, c := range eligible {
		c.decl.Name = ast.NewIdent("_")
		c.decl.Body = ah.BlockStmt()
		c.decl.Recv = nil
		c.decl.Type = &ast.FuncType{Params: &ast.FieldList{}}
	}

	newFileName = virtualizeFileName
	return
}
