#!/usr/bin/env bash
# Simulator for the stage-DECOMPOSITION CPU designs (5stage_cpu_dec.ivy and its
# successors).  These differ from the reference-tagging designs in two ways that
# matter for simulation, so they need their own driver rather than sim_cpu.sh:
#
#   * they have a SEPARATE instruction memory `imem` (in the fetch stage) and
#     data memory `mem` (in the memory stage), so the program is injected into
#     `\imem`, not `\mem`;
#   * every pipeline stage is its own isolate -> its own RTL module, so the
#     emitted netlist is HIERARCHICAL and must be `flatten`ed before `sim`.
#
# The program is NOT baked into the Ivy source (imem is left uninitialized in the
# emitted RTL, so the proof holds for every program); it is injected here at the
# RTL boundary as a $meminit for \imem.
#
#   ./sim_cpu_dec.sh <design[.ivy]> [prog.hex] [cycles] [extra_signals]
#
#     design         design base name or .ivy path (default 5stage_cpu_dec)
#     prog.hex       program as 16-bit hex words, one per address (default prog.hex)
#     cycles         number of clock cycles to simulate       (default 40)
#     extra_signals  comma-separated extra signal names to tabulate per cycle
#                    (matched by suffix, e.g. "d_valid,e_valid,ex_stall"); the
#                    program counter is always shown
#
# Pipeline: ivy_to_rtl -> inject program into \imem -> yosys (flatten) sim -> VCD.
# Writes <design>.vcd and prints the pc trace (stalls collapsed) plus a per-cycle
# table of pc and any requested extra signals.
set -e
cd "$(dirname "$0")"

DESIGN="${1:-5stage_cpu_dec}"
BASE="$(basename "${DESIGN%.ivy}")"        # strip dir and .ivy -> base name
PROG="${2:-prog.hex}"
CYCLES="${3:-40}"
EXTRA="${4:-}"

[ -f "$BASE.ivy" ] || { echo "no such design: $BASE.ivy" >&2; exit 1; }
[ -f "$PROG" ]     || { echo "no such program: $PROG"    >&2; exit 1; }

# 1. Emit RTLIL (ivy_to_rtl writes <BASE>.il).  2. Inject the program into \imem.
ivy_to_rtl "$BASE.ivy" >/dev/null
python3 load_program.py "$BASE.il" "$PROG" "${BASE}_prog.il" imem

# 3. Simulate.  `flatten` collapses the per-stage modules into one; the exported
# action `posedge` is the clock and `rst` is the reset.
yosys -q -p "read_rtlil ${BASE}_prog.il; hierarchy -top cpu; flatten; proc; \
             memory_collect; sim -clock posedge -reset rst -n $CYCLES -vcd ${BASE}.vcd"

# 4. Report.  Signal names in the flattened VCD carry a stage prefix (the pc is
# `if_stage.pc`), so requested names are matched by suffix: a name `s` matches a
# VCD signal called `s` or one ending in `.s`.
python3 - "${BASE}.vcd" "$EXTRA" <<'PY'
import sys, re
vcd = open(sys.argv[1]).read()
want = ['pc'] + [s for s in sys.argv[2].split(',') if s]

def matches(name, s):
    return name == s or name.endswith('.' + s)

# Map each requested signal to its VCD identifier code (first suffix match wins).
code = {}
for m in re.finditer(r'\$var\s+\w+\s+(\d+)\s+(\S+)\s+(\S+?)(?:\s+\[[^\]]*\])?\s+\$end', vcd):
    w, c, name = int(m.group(1)), m.group(2), m.group(3)
    for s in want:
        if s not in code and matches(name, s):
            code[s] = c
missing = [s for s in want if s not in code]
if 'pc' in missing:
    sys.exit("pc signal not found in VCD (looked for `pc` or `*.pc`)")
if missing:
    print("  (signals not found, skipped: %s)" % ', '.join(missing))

rev = {c: n for n, c in code.items()}
def val(bits):
    return int(bits, 2) if set(bits) <= set('01') else 'x'

# Walk the value-change stream, snapshotting the wanted signals at each #time.
cur = {n: 'x' for n in code}
snaps = []; t = 0
def snap():
    if snaps and snaps[-1][0] == t: snaps[-1] = (t, dict(cur))
    else: snaps.append((t, dict(cur)))
for line in vcd.splitlines():
    if line.startswith('#'):
        snap(); t = int(line[1:])
    elif line[:1] == 'b':
        mm = re.match(r'b([01xzZ]+)\s+(\S+)$', line)
        if mm and mm.group(2) in rev: cur[rev[mm.group(2)]] = val(mm.group(1))
    elif line[:1] in '01xzZ' and len(line) >= 2:
        c = line[1:]
        if c in rev: cur[rev[c]] = int(line[0]) if line[0] in '01' else 'x'
snap()

names = [n for n in want if n in code]
print("=== pc trace (stalls collapsed) ===")
seq, prev = [], object()
for _, v in snaps:
    if v['pc'] != prev: seq.append(v['pc']); prev = v['pc']
print("  " + " -> ".join(str(x) for x in seq))

print("=== per-cycle signals ===")
print("  " + "  ".join(f"{n:>10}" for n in ['t'] + names))
prevrow = None
for tt, v in snaps:
    row = tuple(v[n] for n in names)
    if row == prevrow: continue      # collapse unchanged rows
    prevrow = row
    print("  " + "  ".join([f"{tt:>10}"] + [f"{str(v[n]):>10}" for n in names]))
PY
