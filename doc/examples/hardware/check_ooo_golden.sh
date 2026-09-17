#!/usr/bin/env bash
# Combinational equivalence check of the hand-written golden model of the
# stage-1 out-of-order CPU (ooo_alu_golden.sv) against the Ivy-generated RTL
# (ooo_cpu_ref.il, from ivy_to_rtl ooo_cpu_ref.ivy), using rtlil_eqv.
#
# The design has no outputs, so "equivalent" means: from any equal register
# state, every register's next-state function agrees (registers are the cut
# points; rtlil_eqv pairs them by name, memories included after memory_map).
#
#   ./check_ooo_golden.sh            # translate, elaborate the golden, compare
set -e
cd "$(dirname "$0")"

ivy_to_rtl ooo_cpu_ref.ivy >/dev/null
yosys -q -p "read_verilog -sv ooo_alu_golden.sv; hierarchy -top cpu; proc; write_rtlil ooo_alu_golden.il"

cat > ooo_alu_golden.ileq <<EOF
[gold]
file = ooo_alu_golden.il
top  = cpu
clk  = posedge
rst  = rst
[gate]
file = ooo_cpu_ref.il
top  = cpu
clk  = posedge
rst  = rst
EOF

if command -v rtlil_eqv >/dev/null 2>&1; then
    rtlil_eqv ooo_alu_golden.ileq
else
    ( cd ../../.. && python3 -m ivy.ivy_rtlil_eqv doc/examples/hardware/ooo_alu_golden.ileq )
fi
