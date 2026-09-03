#!/usr/bin/env bash
# Simulator for the cache stage-DECOMPOSITION CPU (5stage_cache_cpu_dec.ivy).
# Like sim_cpu_dec.sh, but the cache design has a SINGLE unified memory \mem (the
# I-cache and D-cache both sit in front of it), so the program is injected into
# \mem rather than \imem.  It also samples signals at each RISING CLOCK EDGE (true
# cycles) and prints regression-friendly summary lines:
#
#     PC: <fetch-pc trace, consecutive duplicates collapsed>
#     WB: r<d>=<val> ...   (committed register writes, in retirement order)
#     IFETCH_STALL_CYCLES: <n>   (cycles the I-cache stalled fetch -- cold misses)
#     DMEM_STALL_CYCLES:  <n>    (cycles the D-cache stalled MEM  -- cold misses)
#
# so a `to_rtl` regression can grep the cache's functional AND timing behavior.
#
#   ./sim_cache_cpu_dec.sh <design[.ivy]> [prog.hex] [cycles]
#
# Pipeline: ivy_to_rtl -> inject program into \mem -> yosys (flatten) sim -> VCD.
set -e
cd "$(dirname "$0")"

DESIGN="${1:-5stage_cache_cpu_dec}"
BASE="$(basename "${DESIGN%.ivy}")"
PROG="${2:-t_dcache.hex}"
CYCLES="${3:-50}"

[ -f "$BASE.ivy" ] || { echo "no such design: $BASE.ivy" >&2; exit 1; }
[ -f "$PROG" ]     || { echo "no such program: $PROG"    >&2; exit 1; }

ivy_to_rtl "$BASE.ivy" >/dev/null
python3 load_program.py "$BASE.il" "$PROG" "${BASE}_prog.il" mem >/dev/null
yosys -q -p "read_rtlil ${BASE}_prog.il; hierarchy -top cpu; flatten; proc; \
             memory_collect; sim -clock posedge -reset rst -n $CYCLES -vcd ${BASE}.vcd"

python3 - "${BASE}.vcd" <<'PY'
import sys, re
vcd = open(sys.argv[1]).read()
# The signals we track (matched by exact name or `.<suffix>` in the flat VCD).
want = ['pc', 'ifetch_stall', 'dmem_stall', 'wb_we', 'wb_rd', 'wb_val']
CLK = 'posedge'
def matches(name, s): return name == s or name.endswith('.' + s)
code = {}; clkcode = None
for m in re.finditer(r'\$var\s+\w+\s+(\d+)\s+(\S+)\s+(\S+?)(?:\s+\[[^\]]*\])?\s+\$end', vcd):
    c, name = m.group(2), m.group(3)
    if name == CLK and clkcode is None: clkcode = c
    for s in want:
        if s not in code and matches(name, s): code[s] = c
rev = {c: n for n, c in code.items()}
def val(bits): return int(bits, 2) if set(bits) <= set('01') else 'x'
cur = {n: 'x' for n in code}; clk = 0; cycles = []
def apply(c, v):
    global clk
    if c == clkcode:
        nc = v if v in (0, 1) else 0
        if clk == 0 and nc == 1: cycles.append(dict(cur))
        clk = nc
    elif c in rev:
        cur[rev[c]] = v
for line in vcd.splitlines():
    if not line or line[0] == '#': continue
    if line[0] == 'b':
        mm = re.match(r'b([01xzZ]+)\s+(\S+)$', line)
        if mm: apply(mm.group(2), val(mm.group(1)))
    elif line[0] in '01xzZ' and len(line) >= 2:
        apply(line[1:], int(line[0]) if line[0] in '01' else 'x')

# PC trace (collapse consecutive duplicates).
seq, prev = [], object()
for v in cycles:
    if v.get('pc') != prev: seq.append(v.get('pc')); prev = v.get('pc')
print("PC: " + " -> ".join(str(x) for x in seq))

# Committed register writes (wb_we=1), collapsing stall-held duplicates.
wb, last = [], None
for v in cycles:
    if v.get('wb_we') == 1:
        e = (v.get('wb_rd'), v.get('wb_val'))
        if e != last: wb.append("r%s=%s" % e); last = e
    else:
        last = None
print("WB: " + " ".join(wb))

print("IFETCH_STALL_CYCLES: %d" % sum(1 for v in cycles if v.get('ifetch_stall') == 1))
print("DMEM_STALL_CYCLES: %d"  % sum(1 for v in cycles if v.get('dmem_stall') == 1))
PY
