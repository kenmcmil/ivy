#!/usr/bin/env bash
# Simulate the hand-written golden SystemVerilog model of 5stage_gen_cache_cpu_ref
# (cpu_gen_golden.sv) on a program, as a functional sanity check independent of
# ivy_to_rtl. Injects the program into the idcache main memory (\real_mem), runs
# yosys sim, and prints the same summary lines as sim_cache_cpu_dec.sh:
#   PC:  <fetch-pc trace, consecutive duplicates collapsed>
#   WB:  r<d>=<val> ...   (committed register writes, in retirement order)
#   IFETCH_STALL_CYCLES / DMEM_STALL_CYCLES  (cold-miss stall cycles)
#
#   ./sim_gen_golden.sh [prog.hex] [cycles]
set -e
cd "$(dirname "$0")"
PROG="${1:-icache_prog.hex}"
CYCLES="${2:-50}"
[ -f "$PROG" ] || { echo "no such program: $PROG" >&2; exit 1; }

# 1. Elaborate the golden model to hierarchical RTLIL (main_mem keeps \real_mem so
#    load_program can find it), 2. inject the program, 3. flatten + sim.
yosys -q -p "read_verilog -sv cpu_gen_golden.sv; hierarchy -top cpu; proc; \
             write_rtlil golden_gen.il"
python3 load_program.py golden_gen.il "$PROG" golden_gen_prog.il real_mem >/dev/null
yosys -q -p "read_rtlil golden_gen_prog.il; hierarchy -top cpu; flatten; proc; \
             memory_collect; sim -clock posedge -reset rst -n $CYCLES -vcd golden_gen.vcd"

python3 - golden_gen.vcd <<'PY'
import sys, re
vcd = open(sys.argv[1]).read()
want = ['pc', 'ifetch_stall', 'dmem_stall', 'w_valid', 'w_opcode', 'w_rd', 'w_val']
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

seq, prev = [], object()
for v in cycles:
    if v.get('pc') != prev: seq.append(v.get('pc')); prev = v.get('pc')
print("PC: " + " -> ".join(str(x) for x in seq))

# a WB register write happens when w_valid and w_opcode in {1,2,3,4} (ADD/SUB/LI/LD)
wb, last = [], None
for v in cycles:
    we = (v.get('w_valid') == 1) and (v.get('w_opcode') in (1, 2, 3, 4))
    if we:
        e = (v.get('w_rd'), v.get('w_val'))
        if e != last: wb.append("r%s=%s" % e); last = e
    else:
        last = None
print("WB: " + " ".join(wb))

print("IFETCH_STALL_CYCLES: %d" % sum(1 for v in cycles if v.get('ifetch_stall') == 1))
print("DMEM_STALL_CYCLES: %d"  % sum(1 for v in cycles if v.get('dmem_stall') == 1))
PY
