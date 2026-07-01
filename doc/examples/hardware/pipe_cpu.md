---
layout: page
title: Simple CPU pipeline
---

The file `doc/examples/hardware/pipe_cpu.ivy` models a very simple
two-stage pipelined processor. It brings together all of the hardware
features of Ivy --- wires, registers, arrays (a register file and
memories), a clock and reset, and a memory initializer that loads a
program --- in one design that translates to RTL and can be simulated.

The instruction set
-------------------

Instructions are 16 bits wide, with fixed fields:

    [15:13] opcode   [12:10] rd   [9:7] ra   [6:4] rb   [7:0] imm/target

There are seven opcodes:

| opcode | mnemonic | effect |
|--------|----------|--------|
| 0 | `NOP`  |  --- |
| 1 | `ADD  rd, ra, rb` | `rf[rd] := rf[ra] + rf[rb]` |
| 2 | `SUB  rd, ra, rb` | `rf[rd] := rf[ra] - rf[rb]` |
| 3 | `LI   rd, imm`    | `rf[rd] := zero_extend(imm8)` |
| 4 | `LD   rd, [ra]`   | `rf[rd] := mem[ rf[ra] ]` |
| 5 | `ST   [ra], rb`   | `mem[ rf[ra] ] := rf[rb]` |
| 6 | `BEQZ ra, target` | if `rf[ra] == 0` then `pc := target` |

The design uses three interpreted types: a 16-bit `word` (data and
instructions), an 8-bit `addr` (the program counter and memory addresses),
and a 3-bit `reg` (a register-file index).

Architectural state and the pipeline register
----------------------------------------------

The processor's state consists of the program counter, the register file,
data memory and an instruction ROM (the last three are arrays, and become
RTLIL memories):

    var pc : addr                 # program counter
    var rf(R:reg) : word          # register file
    var mem(A:addr) : word        # data memory
    var imem(A:addr) : word       # instruction memory (ROM; never written)

Between the two pipeline stages sits a pipeline register holding the
instruction currently being executed and a bit saying whether it is real
(as opposed to a squashed *bubble*):

    var ir : word                 # instruction being executed in X
    var ir_valid : bool           # false => bubble

The two stages
--------------

The **fetch** stage (F) is combinational: it reads the instruction at the
current PC from the instruction ROM.

    wire fetched : word
    definition fetched = imem(pc)

The **execute** stage (X) works on the instruction fetched on the
*previous* clock, which is held in `ir`. All of the decoding and the ALU
are combinational, so they are wires. The instruction fields are extracted
with `bfe`, the operands are read from the register file, and the branch
condition is computed:

    wire opcode : opc
    definition opcode = bfe[13][15](ir)
    ...
    wire a_val : word
    definition a_val = rf(ra)
    ...
    wire take_branch : bool
    definition take_branch = ir_valid & (opcode = 6) & (a_val = 0)

Because operands are read *and* results are written in the same stage,
consecutive instructions never race on the register file: there are no
data hazards, and no forwarding is needed.

The state updates happen on the clock edge, in `after posedge`. First the
X-stage instruction is written back (guarded by `ir_valid`, so a bubble
has no effect), and then the PC and pipeline register advance:

    after posedge {
        if ir_valid {
            if opcode = 1 { rf(rd) := a_val + b_val }        # ADD
            else { ... }                                     # SUB / LI / LD / ST
        };
        if take_branch {
            pc := target;          # redirect to the branch target
            ir_valid := false;     # squash the shadow-fetched instruction
        } else {
            pc := pc + 1;
            ir := fetched;
            ir_valid := true;
        }
    }

The control hazard
------------------

The conditional branch is the interesting part. `BEQZ` is resolved in the
execute stage, one cycle *after* it was fetched. By then the fetch stage
has already fetched the next sequential instruction --- the one in the
branch's *shadow*. When the branch is taken, that instruction must not
take effect, so the update sets `ir_valid := false`, turning it into a
one-cycle bubble, while the PC is redirected to the target. This is the
classic control hazard of a pipelined processor, and it costs one cycle
per taken branch.

Reset and loading a program
---------------------------

`after init` gives the reset/power-on behavior. It clears the PC and the
pipeline valid bit, zeroes the register file (a broadcast assignment over
the index variable `R`), and loads a small program into the instruction
ROM:

    after init {
        pc := 0;
        ir_valid := false;
        rf(R) := 0;            # zero the register file
        imem(0) := 0x6405;     # LI   r1, 5
        imem(1) := 0x6801;     # LI   r2, 1
        imem(2) := 0x44a0;     # SUB  r1, r1, r2
        imem(3) := 0xc002;     # BEQZ r0, 2   (r0 == 0, so an unconditional jump to 2)
    }

The register/PC resets become synchronous-reset logic driven by the global
`rst`; the memory assignments become power-on memory contents. So this one
Ivy file is a self-contained processor *with* its program.

Finally, so the design has an observable output, the current PC is exposed
as an export wire:

    export wire pc_out : addr
    definition pc_out = pc

Translating and simulating
--------------------------

Translate the design to RTLIL in the usual way:

    $ ivy_to_rtl pipe_cpu.ivy

The register file and the two memories become RTLIL memories, and the
program becomes `$meminit_v2` cells:

    $ grep 'memory\|meminit' pipe_cpu.il
      memory width 16 size 256 \imem
      memory width 16 size 256 \mem
      memory width 16 size 8 \rf
      cell $meminit_v2 $meminit$imem$21   # imem[0] = 0x6405
      ...

Because the program is baked in, we can simulate directly, with no
hand-written stimulus beyond the clock and reset:

    $ yosys -p "read_rtlil pipe_cpu.il; hierarchy -top cpu; proc; memory_collect;
                sim -clock posedge -reset rst -n 12 -vcd cpu.vcd"

Reading `pc_out` from `cpu.vcd`, the program-counter trace after reset is:

    0, 1, 2, 3, 4, 2, 3, 4, 2, 3, 4, ...

The processor fetches `0, 1, 2, 3` sequentially. The `BEQZ` at address 3
is resolved in the execute stage while address 4 is being fetched, so the
PC visits 4 (whose instruction is then squashed) before redirecting to the
branch target 2 --- the `3, 4, 2` in the trace is exactly the one-cycle
branch bubble. The loop `2, 3, 4` then repeats, decrementing `r1` through
the `SUB` at address 2 on each pass.

Limitations
-----------

This is deliberately a minimal example. In particular there is no
instruction memory port for loading code at run time (the ROM is fixed by
the initializer), the `LD`/`ST` address is only the low 8 bits of a
register, and the branch is unconditional-friendly only because the
register file is zeroed at reset. It is meant to illustrate the Ivy
hardware features and the RTL translation end to end, not to be a complete
CPU.
