# Repository Guidelines

## Project Structure & Module Organization
- `ivy/`: core Python sources (parsing, logic, SMT, UI, C++ extraction). See `ivy/README.md` for a code tour.
- `include/`: IVy include libraries and headers used by extraction.
- `doc/`: documentation and tutorials (commands, install, examples).
- `examples/` and `doc/examples/`: sample IVy specs and walkthroughs.
- `test/`: regression tests (`*.ivy`, helper `*.py`, and shell tests).
- `submodules/`: external dependencies (e.g., Z3, picotls, abc, aiger).
- Top-level build scripts: `build_submodules.py`, `build_v2_compiler.py`, `setup.py`.

## Build, Test, and Development Commands
- `python3 build_submodules.py`: builds bundled submodules (Z3, picotls, aiger, abc).
- `sudo python3 setup.py install`: install Ivy into system Python.
- `sudo python3 setup.py develop`: editable install for development.
- `python build_v2_compiler.py`: optional Ivy v2 compiler build.
- `ivy_check trace=true path/to/file.ivy`: run proof checks with a counterexample trace on failure.
- `ivy_to_cpp target=repl path/to/file.ivy`: extract an IVy program to C++ REPL.
- `cd test && ./runall`: run Python + shell regression tests in `test/`.

## Coding Style & Naming Conventions
- Python sources use 4-space indentation and standard snake_case names.
- Prefer minimal, local changes that match surrounding style and imports.
- No formatter or linter is configured in-repo; keep diffs small and readable.
- IVy source files use the `.ivy` extension (see `doc/language.md` for syntax).

## Testing Guidelines
- Tests live in `test/` and are mostly `.ivy` files plus Python helpers.
- `test/runall` executes `*.py` tests and `tilelink_unit_test.sh` with timeouts.
- C++ extraction tests can be built via `test/Makefile` patterns, e.g.:
  - `make foo.cpp` (from `foo.ivy`)
  - `make foo.test` (C++ test harness)

## Commit & Pull Request Guidelines
- Recent commits use short, imperative, lowercase subjects (e.g., “add tdl example”).
- No PR template is present; include a brief summary, motivation, and tests run.
- Link related issues or papers when relevant and call out any new dependencies.

## Security & Configuration Tips
- Installation expects Python 3 and system dependencies listed in `doc/install.md`.
- Submodules are required for full functionality; ensure recursive clone or run the build script.
