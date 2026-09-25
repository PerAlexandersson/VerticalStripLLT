# First-east bounce geometry

This is a geometry plan, not a proof of the generic bounce value identities.
It incorporates Terra's independent read-only audit and primary's correction
of the insufficient fixed-word, weak-gap state. Source: immutable manuscript
lines 1853–1993, particularly the strict inequality at line 1890.

Let Y be the prefix before the first east step, ending in a diagonal. Put
b = length Y and a = diagonalCount Y. Since Y has no east, its endpoint is
(a,b). The non-product branch supplies a+1<b. A bounce returns at height a,
so its incident steps have indices a−1 and a. The last diagonal is at b−1;
the strict gap makes it distinct from both inspected steps.

Use a seed carrying no east, a final diagonal, and diagonalCount Y+1<length Y.
No path validity is needed for these word facts. Retain full path validity
in a separate outer certificate for the later semantic transformations.

Split the seed as Y = U s t V d, with length U+1 = diagonalCount Y.
The two inspected steps are north or diagonal. The nn, nd, dn pairs stop.
For dd, the child prefix is U d, equivalently Y.take a. The leaving diagonal
and final diagonal are both outside the child. Thus, writing c for the
child's diagonal count, c+2≤a and hence c+1<a. The child inherits no-east,
final-diagonal, and strict-gap conditions. Its length is a<b, so recursion
terminates by prefix length. A fixed original word and the weaker c<a alone
do not justify the required child gap.

First bounded implementation: `BounceSeed`, a seed split theorem with exact
return index and no-east subwords, and a dd-child constructor with its strict
length decrease. A later inductive trace can retain these decompositions,
avoiding repeated dependent indexing. A terminal trace gives U s t V d;
peeling a dd parent gives the source's U s t V' dd V'' d decomposition.

The nd semantic branch for an arbitrary restricted-recurrence witness is
still open; see `RESTRICTED_BOUNCE_AUDIT.md`. Geometry must not smuggle in an
unrestricted recurrence, uniqueness, or the coloring-specific third bounce.
