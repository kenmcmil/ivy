#!/usr/bin/env bash
# Combinational equivalence check of a hand-written golden model of the
# out-of-order CPU against the Ivy-generated RTL, using rtlil_eqv.
#
#   ./check_ooo_golden.sh [design[.ivy]] [golden.sv]
#
#     default: ooo_cpu_alu_ref.ivy vs ooo_alu_golden.sv   (stage 1, ALU only)
#     stage 2: ./check_ooo_golden.sh ooo_cpu_beqz_ref ooo_beqz_golden.sv
#     stage 3a: ./check_ooo_golden.sh ooo_cpu_mem_ref ooo_mem_golden.sv
#     stage 3b: ./check_ooo_golden.sh ooo_cpu_lsq_ref ooo_lsq_golden.sv
#     stage 3c: ./check_ooo_golden.sh ooo_cpu_ref ooo_fwd_golden.sv
#
# The design has no outputs, so "equivalent" means: from any equal register
# state, every register's next-state function agrees (registers are the cut
# points; rtlil_eqv pairs them by name -- memories included after memory_map,
# and the predictor's bp.bht after flattening).
#
# The golden is elaborated with plain `proc` (no memory_dff: that would fold
# read-side registers into synchronous read ports and break the boundary);
# rtlil_eqv itself ignores the dead write-port temporaries proc leaves behind.
set -e
cd "$(dirname "$0")"

DESIGN="$(basename "${1:-ooo_cpu_alu_ref}" .ivy)"
GOLDEN="${2:-ooo_alu_golden.sv}"
GBASE="$(basename "$GOLDEN" .sv)"

ivy_to_rtl "$DESIGN.ivy" >/dev/null
yosys -q -p "read_verilog -sv $GOLDEN; hierarchy -top cpu; proc; write_rtlil $GBASE.il"

cat > "$GBASE.ileq" <<CFG
[gold]
file = $GBASE.il
top  = cpu
clk  = posedge
rst  = rst
[gate]
file = $DESIGN.il
top  = cpu
clk  = posedge
rst  = rst
CFG

if command -v rtlil_eqv >/dev/null 2>&1; then
    rtlil_eqv "$GBASE.ileq"
else
    ( cd ../../.. && python3 -m ivy.ivy_rtlil_eqv "doc/examples/hardware/$GBASE.ileq" )
fi
