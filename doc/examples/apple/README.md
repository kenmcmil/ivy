This directory contains two liveness proofs of the Apple generic memory model
in Ivy. The models and proofs can be found in these files:

- `ord_live.ivy`: Proof broken into lemmas
- `ord_live2.ivy`: Proof using one instance of lexicographic liveness rule

The proofs can be checked with this command:

```
$ ivy_check complete=fo <file>.ivy
```

The option `complete=fo` disables the check that the VC's are in EPR,
which saves a bit of time. Of course, run times in virtualbox will not
match the run times given in the paper.

Then liveness proof in each file begins with the comment 'Liveness
proof starts here'. Comments in the files describe the structure of
the proof and the Ivy tactics used. In the first proof, `ord_live.ivy`,
the model checking tactic `mc` is used to discharge two lemmas. This
tactic is beyond the scope of the paper and is described in [1].

The lemma proofs use Ivy tactics having names beginning with
`l2s_auto`. These are early versions of a liveness proof rule with
relational rankings that were developed in the process of constructing
the proof.

[1] Kenneth L. McMillan. Eager abstraction for symbolic model checking. In
Hana Chockler and Georg Weissenbacher, editors, Computer Aided
Verification - 30th International Confer- ence, CAV 2018, Held as Part
of the Federated Logic Conference, FloC 2018, Oxford, UK, July 14-17,
2018, Proceedings, Part I, volume 10981 of Lecture Notes in Computer
Science, pages 191–208. Springer, 2018.

