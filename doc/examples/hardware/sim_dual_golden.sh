#!/usr/bin/env bash
# Simulate the hand-written golden SystemVerilog model of dual_issue_cpu_ref
# (dual_issue_golden.sv) on a program, as a functional sanity check independent
# of ivy_to_rtl -- the counterpart of sim_cpu.sh (which sims the Ivy RTL). It
# elaborates the golden, injects the program into the idcache main memory
# (\real_mem, inside idc.main_mem), runs yosys sim, and prints the pc trace with
# consecutive duplicates collapsed -- the same signature the dual_issue
# regression checks (e.g. "2 -> 4 -> 6" = a dual-issue bundle stepping pc by 2).
#
#   ./sim_dual_golden.sh [prog.hex] [cycles]
set -e
cd "$(dirname "$0")"
PROG="${1:-dual_dep_prog.hex}"
CYCLES="${2:-40}"
[ -f "$PROG" ] || { echo "no such program: $PROG" >&2; exit 1; }

# 1. Elaborate the golden to hierarchical RTLIL (main_mem keeps \real_mem so
#    load_program can find it), 2. inject the program, 3. flatten + sim.
yosys -q -p "read_verilog -sv dual_issue_golden.sv; hierarchy -top cpu; proc; \
             write_rtlil dual_golden.il"
python3 load_program.py dual_golden.il "$PROG" dual_golden_prog.il real_mem >/dev/null
yosys -q -p "read_rtlil dual_golden_prog.il; hierarchy -top cpu; proc; memory_collect; \
             sim -clock posedge -reset rst -n $CYCLES -vcd dual_golden.vcd"

python3 - dual_golden.vcd <<'PY'
import sys, re
vcd = open(sys.argv[1]).read()
code = None
for m in re.finditer(r'\$var\s+\w+\s+(\d+)\s+(\S+)\s+(\S+?)(?:\s+\[[^\]]*\])?\s+\$end', vcd):
    w, c, name = int(m.group(1)), m.group(2), m.group(3)
    if name == 'pc' and code is None: code = c
if code is None: sys.exit("pc signal not found in VCD")
cur = 'x'; snaps = []; t = 0
def snap():
    if snaps and snaps[-1][0] == t: snaps[-1] = (t, cur)
    else: snaps.append((t, cur))
for line in vcd.splitlines():
    if line.startswith('#'):
        snap(); t = int(line[1:])
    elif line[:1] == 'b':
        mm = re.match(r'b([01xzZ]+)\s+(\S+)$', line)
        if mm and mm.group(2) == code:
            cur = int(mm.group(1), 2) if set(mm.group(1)) <= set('01') else 'x'
snap()
seq, prev = [], object()
for _, v in snaps:
    if v != prev: seq.append(v); prev = v
print("PC: " + " -> ".join(str(x) for x in seq))
PY
