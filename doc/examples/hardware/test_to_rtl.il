# RTLIL (Yosys) reference output for test_to_rtl.ivy
#
# This is the expected result of `ivy_to_rtl test_to_rtl.ivy`. The Ivy
# object hierarchy
#
#     top
#       top.inc      (combinational: out = inp + 1)
#       top.delay    (register:      out = old(inp))
#
# maps to three RTLIL modules. Ports are numbered in declaration order;
# the global clock `posedge` (one per exported action) and the global
# reset `rst` are routed in as additional inputs of every block that has
# state.

autoidx 1

# Top-level module. `inp` is the top-level input (import wire) and `out`
# is the top-level output (export wire). The auxiliary wire `tmp` carries
# the output of `inc` to the input of `delay` (the definition
# `delay.inp = inc.out`).
module \top
  wire width 8 input 1 \inp
  wire width 8 output 2 \out
  wire input 3 \posedge
  wire input 4 \rst
  wire width 8 \tmp
  cell \inc \inc
    connect \inp \inp
    connect \out \tmp
  end
  cell \delay \delay
    connect \inp \tmp
    connect \posedge \posedge
    connect \rst \rst
    connect \out \out
  end
end

# Combinational submodule: out = inp + 1. The `+` operator becomes an
# $add cell with an 8-bit constant 1 on its B input.
module \inc
  wire width 8 input 1 \inp
  wire width 8 output 2 \out
  cell $add $add$inc
    parameter \A_SIGNED 0
    parameter \B_SIGNED 0
    parameter \A_WIDTH 8
    parameter \B_WIDTH 8
    parameter \Y_WIDTH 8
    connect \A \inp
    connect \B 8'00000001
    connect \Y \out
  end
end

# Sequential submodule: a register. The state variable `val` becomes a
# D flip-flop clocked by `posedge`. The initializer `val := 0` becomes
# synchronous reset logic: a multiplexer selects the reset value 0 when
# `rst` is asserted and the action update `inp` otherwise. The output
# wire `out` is driven directly from `val`.
module \delay
  wire width 8 input 1 \inp
  wire width 8 output 2 \out
  wire input 3 \posedge
  wire input 4 \rst
  wire width 8 \val
  wire width 8 \d
  cell $mux $mux$delay
    parameter \WIDTH 8
    connect \A \inp
    connect \B 8'00000000
    connect \S \rst
    connect \Y \d
  end
  cell $dff $dff$delay
    parameter \WIDTH 8
    parameter \CLK_POLARITY 1
    connect \CLK \posedge
    connect \D \d
    connect \Q \val
  end
  connect \out \val
end
