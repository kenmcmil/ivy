#!/usr/bin/env python3
"""Inject a program into an ivy_to_rtl netlist for simulation.

The cache-CPU model (5stage_cache_cpu_ref.ivy) initializes its main memory from
an *uninterpreted* function `init_mem`, so the correctness proof holds for every
program.  Because `init_mem` is uninterpreted, `ivy_to_rtl` emits the main-memory
array `\\mem` with no `$meminit` -- i.e. the program is deliberately NOT baked
into the RTL.  To simulate a particular program you supply it here, at the RTL
boundary, as a `$meminit` cell built from an external hex file.  The Ivy source
stays program-free.

    load_program.py <in.il> <prog.hex> <out.il> [mem_name]

`prog.hex` holds the program as 16-bit hex words, one word per address starting
at 0.  Blank lines and `#` comments (whole-line or trailing) are ignored, and a
`0x` prefix is allowed, so the file can be annotated:

    6405        # 0: LI   r1, 5
    0x6801      # 1: LI   r2, 1
    44a0        # 2: SUB  r1, r1, r2
    c002        # 3: BEQZ r0, 2   (loops to 2)
"""
import sys, re

def main():
    if len(sys.argv) < 4:
        sys.exit(__doc__)
    infile, hexfile, outfile = sys.argv[1], sys.argv[2], sys.argv[3]
    mem = sys.argv[4] if len(sys.argv) > 4 else 'mem'

    words = []
    for line in open(hexfile):
        line = line.split('#', 1)[0]          # strip comments
        for tok in line.split():
            words.append(int(tok, 16) & 0xFFFF)
    if not words:
        sys.exit('no program words in ' + hexfile)

    il = open(infile).read()
    m = re.search(r'^\s*memory width (\d+) size (\d+) \\' + re.escape(mem) + r'\s*$',
                  il, re.M)
    if not m:
        sys.exit('memory \\%s not found in %s' % (mem, infile))
    width, size = int(m.group(1)), int(m.group(2))
    abits = max(1, (size - 1).bit_length())
    if len(words) > size:
        sys.exit('program has %d words but \\%s holds only %d' % (len(words), mem, size))

    # $meminit DATA packs word 0 in the low bits, so emit words MSB-first (last first).
    data = ''.join(format(w, '0{}b'.format(width)) for w in reversed(words))
    cell = (
        '  cell $meminit_v2 $meminit${m}$prog\n'
        '    parameter \\MEMID "\\\\{m}"\n'
        '    parameter \\ABITS {ab}\n'
        '    parameter \\WIDTH {w}\n'
        '    parameter \\WORDS {n}\n'
        '    parameter \\PRIORITY 0\n'
        "    connect \\ADDR {ab}'{addr}\n"
        "    connect \\DATA {dw}'{data}\n"
        "    connect \\EN {w}'{en}\n"
        '  end\n'
    ).format(m=mem, ab=abits, w=width, n=len(words),
             addr='0' * abits, dw=len(words) * width, data=data, en='1' * width)

    open(outfile, 'w').write(il[:m.end()] + '\n' + cell + il[m.end():])
    print('injected $meminit for \\%s: %d words (width %d) -> %s'
          % (mem, len(words), width, outfile))

main()
