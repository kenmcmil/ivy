#!/usr/bin/env bash
# Simulate 5stage_cache_cpu_ref with a program supplied at the RTL boundary,
# so the program is NOT baked into the Ivy source (the proof holds for every
# program; main memory is left uninitialized in the emitted RTL).
#
#   ./sim_cache_cpu.sh [prog.hex] [cycles]
#
# Steps: ivy_to_rtl -> inject the program as a $meminit for \mem -> yosys sim.
# Writes cpu.vcd and prints the program-counter trace.
set -e
cd "$(dirname "$0")"

PROG="${1:-prog.hex}"
CYCLES="${2:-40}"
BASE=5stage_cache_cpu_ref

ivy_to_rtl "$BASE.ivy" >/dev/null
python3 load_program.py "$BASE.il" "$PROG" "${BASE}_prog.il"

yosys -q -p "read_rtlil ${BASE}_prog.il; hierarchy -top cpu; proc; memory_collect; \
             sim -clock posedge -reset rst -n $CYCLES -vcd cpu.vcd"

echo "=== program-counter trace (from cpu.vcd) ==="
python3 - cpu.vcd <<'PY'
import sys, re
vcd = open(sys.argv[1]).read()
# pc is an 8-bit signal (a reg in this design); find its VCD identifier by name
m = re.search(r'\$var\s+\w+\s+8\s+(\S+)\s+pc\s', vcd)
if not m:
    sys.exit("pc signal not found in VCD")
code, t, seq = m.group(1), 0, []
for line in vcd.splitlines():
    if line.startswith('#'):
        t = int(line[1:])
    elif line[:1] == 'b':
        mm = re.match(r'b([01xz]+)\s+(\S+)$', line)
        if mm and mm.group(2) == code:
            v = mm.group(1)
            seq.append((t, int(v, 2) if set(v) <= set('01') else 'x'))
out = []
for t, v in seq:                      # collapse stalls (repeated values)
    if not out or out[-1] != v:
        out.append(v)
print("  " + " -> ".join(str(v) for v in out))
PY
