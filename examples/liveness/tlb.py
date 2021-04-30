"""
A helper script for program counter bookkeeping for the tlb.ivy
"""

import itertools

cs = "i1,i2,i3,i4,i5,i6,i7,i8,i9,i11,i12,i14,i15,m2,m3,m5,r1,r2,r3,r5,r6,r7,r8,b1".split(',')

if False:
    for c in cs:
        print "    individual {}:location".format(c)
    for c1,c2 in itertools.combinations(cs,2):
        print "    axiom {} ~= {}".format(c1,c2)
    print "    axiom forall L:location. {}".format(' | '.join('L={}'.format(c) for c in cs))
else:
    for c in cs:
        print "    relation pc_{}(P:processor)".format(c)
    print

    for c1,c2 in itertools.combinations(cs,2):
        print "    invariant ~pc_{}(P) | ~pc_{}(P)".format(c1,c2)
    print

    for c1,c2 in itertools.combinations(cs,2):
        print "    invariant l2s_saved -> ~($l2s_s X. pc_{}(X))(P) | ~($l2s_s X. pc_{}(X))(P)".format(c1,c2)
    print

    print "    invariant {}".format(' | '.join('pc_{}(P)'.format(c) for c in cs))
    print
    print "    invariant {}".format(' | '.join('($l2s_s X. pc_{}(X))(P)'.format(c) for c in cs))
    print

    print "    pc_{}(P) := true;".format(cs[-1])
    for c in cs[:-1]:
        print "    pc_{}(P) := false;".format(c)
    print

"""
Some useful emacs regex's:

pc(\(P1\|P2\|C\|P\|sk0\|sk1\|sk2\)) ?\(~?\)= ?\(b1\|r8\|r7\|r6\|r5\|r3\|r2\|r1\|m5\|m3\|m2\|i15\|i14\|i12\|i11\|i9\|i8\|i7\|i6\|i5\|i4\|i3\|i2\|i1\)

\2pc_\3(\1)

(\$l2s_s P0. pc(P0))(\(P1\|P2\|C\|P\|sk0\|sk1\|sk2\)) ?\(~?\)= ?\(b1\|r8\|r7\|r6\|r5\|r3\|r2\|r1\|m5\|m3\|m2\|i15\|i14\|i12\|i11\|i9\|i8\|i7\|i6\|i5\|i4\|i3\|i2\|i1\)

\2($l2s_s X. pc_\3(X))(\1)

(\$l2s_s P. pc(P))(\(P1\|P2\|C\|P\|sk0\|sk1\|sk2\)) ?\(~?\)= ?\(b1\|r8\|r7\|r6\|r5\|r3\|r2\|r1\|m5\|m3\|m2\|i15\|i14\|i12\|i11\|i9\|i8\|i7\|i6\|i5\|i4\|i3\|i2\|i1\)



"""
