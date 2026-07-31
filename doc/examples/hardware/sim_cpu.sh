#!/usr/bin/env bash
# Generic simulator for the reference-tagging CPU designs.
#
# Works with any design in this directory that (a) implements the shared ISA
# (see the encoding table at the top of the .ivy files) and (b) uses a single
# unified instruction/data memory named `cpu.mem`.  That covers pipe_cpu,
# 5stage_cpu_ref, 5stage_cache_cpu_ref, 5stage_bp_cpu_ref, dual_issue_cpu_ref,
# ... -- the program is NOT baked into the Ivy source (main memory is left
# uninitialized in the emitted RTL, so the proof holds for every program); it
# is injected here at the RTL boundary as a $meminit for \mem.
#
#   ./sim_cpu.sh <design[.ivy]> [prog.hex] [cycles] [extra_signals]
#
#     design         design base name or .ivy path (e.g. dual_issue_cpu_ref)
#     prog.hex       program as 16-bit hex words, one per address (default prog.hex)
#     cycles         number of clock cycles to simulate       (default 40)
#     extra_signals  comma-separated extra signal names to tabulate per cycle
#                    (e.g. "ifill_on,ifill_got,mbusy"); pc is always shown
#
# Pipeline: ivy_to_rtl -> inject program into \mem -> yosys sim -> VCD.
# Writes <design>.vcd and prints the program-counter trace (stalls collapsed),
# plus a per-cycle table of pc and any requested extra signals.
set -e
cd "$(dirname "$0")"

DESIGN="${1:?usage: sim_cpu.sh <design[.ivy]> [prog.hex] [cycles] [extra_signals]}"
BASE="$(basename "${DESIGN%.ivy}")"        # strip dir and .ivy -> base name
PROG="${2:-prog.hex}"
CYCLES="${3:-40}"
EXTRA="${4:-}"

[ -f "$BASE.ivy" ] || { echo "no such design: $BASE.ivy" >&2; exit 1; }
[ -f "$PROG" ]     || { echo "no such program: $PROG"    >&2; exit 1; }

# 1. Emit RTLIL (ivy_to_rtl writes <BASE>.il).  2. Inject the program into \mem.
ivy_to_rtl "$BASE.ivy" >/dev/null
python3 load_program.py "$BASE.il" "$PROG" "${BASE}_prog.il" mem

# 3. Simulate.  The exported action `posedge` is the clock; `rst` is the reset.
yosys -q -p "read_rtlil ${BASE}_prog.il; hierarchy -top cpu; proc; memory_collect; \
             sim -clock posedge -reset rst -n $CYCLES -vcd ${BASE}.vcd"

# 4. Report.  Pull pc (always) and any requested extra signals out of the VCD,
# print the collapsed pc trace and a per-cycle table.
python3 - "${BASE}.vcd" "$EXTRA" <<'PY'
import sys, re
vcd = open(sys.argv[1]).read()
want = ['pc'] + [s for s in sys.argv[2].split(',') if s]

# Map each requested signal name to its VCD identifier code and bit width.
# VCD $var lines look like:  $var reg 8 n20 pc [7:0] $end  /  $var wire 1 n24 ic.fetch_valid $end
code = {}; width = {}
for m in re.finditer(r'\$var\s+\w+\s+(\d+)\s+(\S+)\s+(\S+?)(?:\s+\[[^\]]*\])?\s+\$end', vcd):
    w, c, name = int(m.group(1)), m.group(2), m.group(3)
    if name in want and name not in code:      # first match wins
        code[name], width[name] = c, w
missing = [s for s in want if s not in code]
if 'pc' in missing:
    sys.exit("pc signal not found in VCD (does this design use an 8-bit `pc`?)")
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
hdr = "  " + "  ".join(f"{n:>10}" for n in ['t'] + names)
print(hdr)
prevrow = None
for tt, v in snaps:
    row = tuple(v[n] for n in names)
    if row == prevrow: continue      # collapse unchanged rows
    prevrow = row
    print("  " + "  ".join([f"{tt:>10}"] + [f"{str(v[n]):>10}" for n in names]))
PY
