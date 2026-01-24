# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

IVy is a research tool for interactive development of protocols and their proofs of correctness. It provides:
- Interactive visualization of automated proofs
- A platform for developing automated proof techniques
- Code extraction to C++ for verified implementations

## Build & Installation

### Prerequisites (Ubuntu/Debian)
```bash
sudo apt-get install python3 python3-pip g++ cmake python3-ply python3-pygraphviz git python3-tk tix pkg-config libssl-dev libreadline-dev
```

### Build from source
```bash
git clone --recurse-submodules https://github.com/kenmcmil/ivy.git
cd ivy
python3 build_submodules.py   # builds Z3, picotls, aiger, abc
sudo python3 setup.py install  # or 'develop' for development
```

### Optional: Build v2 compiler
```bash
python build_v2_compiler.py
```

## Key Commands

| Command | Description |
|---------|-------------|
| `ivy_check file.ivy` | Check proof of an IVy program |
| `ivy_check trace=true file.ivy` | Check with counterexample trace on failure |
| `ivy_check diagnose=true file.ivy` | Launch GUI counterexample viewer on failure |
| `ivy_to_cpp target=repl file.ivy` | Extract to C++ REPL |
| `ivy_to_cpp target=test file.ivy` | Extract with randomized tester |
| `ivy file.ivy` | Interactive invariant construction UI |
| `ivy_show file.ivy` | Print elaborated program |

### Common ivy_check options
- `isolate=name` - verify specific isolate
- `complete={epr,qf,fo}` - fragment checker logic (default: epr)
- `seed=N` - set SMT solver random seed
- `macro_finder=true/false` - enable Z3 macro detection

### ivy_to_cpp options
- `target={repl,test,class}` - extraction mode
- `classname=name` - C++ class name
- `build=true` - compile extracted code
- `outdir=path` - output directory

## Architecture

### Core Components (`ivy/`)

**Logic Layer:**
- `logic.py` - AST for IVy's logic
- `ivy_logic.py` - wrapper with logical signatures
- `ivy_logic_utils.py` - utilities built on logic
- `type_inference.py` - type inference

**SMT Interface:**
- `ivy_solver.py` - Z3 SMT solver interface
- `ivy_smtlib.py` - SMTLIB theory definitions

**Language Processing:**
- `ivy_lexer.py` - lexical analyzer
- `ivy_parser.py` - IVy language parser
- `ivy_logic_parser.py` - formula parser
- `ivy_module.py` - internal module representation
- `ivy_compiler.py` - compiles IVy to internal representation

**Verification:**
- `ivy_check.py` - command-line proof checker
- `ivy_isolate.py` - isolate processing
- `ivy_proof.py` - tactical prover
- `ivy_fragment.py` - decidable fragment checker
- `ivy_theory.py` - fragment checker and built-in proof rules

**Code Extraction:**
- `ivy_to_cpp.py` - translator to C++ (255KB, main extractor)
- `ivy_cpp.py` - C++ program representation
- `ivy_cpp_types.py` - IVy types in C++

**GUI/Visualization:**
- `ivy_graph.py` - concept domain graph layout
- `ivy_graph_ui.py` - toolkit-independent graph UI
- `tk_ui.py`, `tk_graph_ui.py` - Tk backend

### Include Files (`ivy/include/`)
- Version-specific IVy libraries (1.5, 1.6, 1.7, 1.8)
- Z3 headers for C++ extraction

### Submodules (`submodules/`)
- `z3` - SMT solver
- `picotls` - TLS library for QUIC examples
- `abc` - logic synthesis for model checking
- `aiger` - AIG format tools for model checking

## Language Notes

- IVy files begin with `#lang ivy1.7` (or 1.8)
- No references/aliasing - modifying `a` never affects `b`
- Synchronous execution model - actions are isolated/atomic
- Three value categories: data values, function values, procedures
- Decidable fragment based on EPR (effectively propositional) logic

## Testing

Run an example:
```bash
cd doc/examples
ivy_check trace=true client_server_example_new.ivy
```

Test files are in `test/` directory. The Makefile pattern:
```makefile
# Compile .ivy to C++ REPL
%.cpp: %.ivy
    ivy_to_cpp target=repl isolate=iso_impl $<

# Compile .ivy to test harness
%.test.cpp: %.ivy
    ivy_to_cpp target=test classname=$*.test $<
```
