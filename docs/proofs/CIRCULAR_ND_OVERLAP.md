# Periodic ND overlap: remaining proof obligation

The ordinary generalized ND reduction must not be projected using an assumed
separation of its initial and terminal strict edges. They may be the same edge
orbit even when all corners are strict and the strict graph is acyclic.

The following manually checked obstruction was found by the independent Astra
review. It is proof-route evidence, not a new formalization milestone or a
counterexample to the full circular expansion.

Take size five and zero-based areas `(2,3,2,3,3)`. All corners are at heads
`1,3,4`. Their strict edges form the chain `0 → 3 → 1 → 4`; vertex `2` is
isolated. The relevant lifted boundary values are

```
z       0   1   2   3   4   5   6   7
b(z)   -2  -2   0   0   1   3   3   5
```

Root `z=6` is eligible DE, with strict length three and east gap one. Its
first contact is `b(6)=3`, a DD contact with east gap zero. Descending gives
terminal ND at `x=0`. Thus `z` and `x+1` have the same residue. Their strict
edge is the same orbit `3 → 1`. The other eligible seed, residue four, restarts
at residue one under the current reverse search, so changing the seed does
not remove the issue in that algorithm.

Simply shortening the root produces strict edges `4 → 1` and `1 → 4`, hence a
zero target. This observation alone does not disprove a suitable linear
identity; it does disprove an acyclicity-based alias-exclusion claim. A second
ordinary row edit cannot be applied without accounting for the repeated orbit.

Required next result: an alias-aware ND identity for both independently defined
polynomials, or an alternative reduction such as an applicable positive-gap
relation. The proof must give actual valid circular target diagrams and a strict
measure decrease. Ordinary disjoint-window geometry is insufficient.

The completed direct NN/DN identities and full DN rank/termination theorem do
not assume this false separation property and remain unaffected.
