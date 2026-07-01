# Hand-written reference for refinement3, structurally name-matched to the
# ivy-generated refinement3.il (same module/instance/port/register names) but
# with the per-bit combinational logic written differently: for a 1-bit
# counter, (val == 1) is just val, and (val + 1) is ~val, i.e. next = val ^ en.
# Equivalence checking must therefore prove the two combinational forms equal.

autoidx 1

module \this
  wire input 1 \en
  wire output 2 \cout
  wire input 3 \posedge
  wire input 4 \rst
  wire \tmp
  wire \c0.cout
  wire \c1.cout
  cell \c0 \c0
    connect \en \en
    connect \cout \c0.cout
    connect \posedge \posedge
    connect \rst \rst
  end
  cell \c1 \c1
    connect \en \tmp
    connect \cout \c1.cout
    connect \posedge \posedge
    connect \rst \rst
  end
  connect \cout \c1.cout
  connect \tmp \c0.cout
end

module \c0
  wire input 1 \en
  wire output 2 \cout
  wire input 3 \posedge
  wire input 4 \rst
  wire \val
  wire \nxt
  wire \d
  cell $and $cout_and
    parameter \A_SIGNED 0
    parameter \B_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \en
    connect \B \val
    connect \Y \cout
  end
  cell $xor $incr
    parameter \A_SIGNED 0
    parameter \B_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \val
    connect \B \en
    connect \Y \nxt
  end
  cell $mux $rstmux
    parameter \WIDTH 1
    connect \A \nxt
    connect \B 1'0
    connect \S \rst
    connect \Y \d
  end
  cell $dff $dff$c0.val
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1
    connect \CLK \posedge
    connect \D \d
    connect \Q \val
  end
end

module \c1
  wire input 1 \en
  wire output 2 \cout
  wire input 3 \posedge
  wire input 4 \rst
  wire \val
  wire \nxt
  wire \d
  cell $and $cout_and
    parameter \A_SIGNED 0
    parameter \B_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \en
    connect \B \val
    connect \Y \cout
  end
  cell $xor $incr
    parameter \A_SIGNED 0
    parameter \B_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \val
    connect \B \en
    connect \Y \nxt
  end
  cell $mux $rstmux
    parameter \WIDTH 1
    connect \A \nxt
    connect \B 1'0
    connect \S \rst
    connect \Y \d
  end
  cell $dff $dff$c1.val
    parameter \WIDTH 1
    parameter \CLK_POLARITY 1
    connect \CLK \posedge
    connect \D \d
    connect \Q \val
  end
end
