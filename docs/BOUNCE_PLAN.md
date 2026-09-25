# Single-bounce proof plan

This is a planned interface, not a proved bounce theorem. Terra independently
audited the author manuscript and current finite-word model; primary reviewed
the proposal. Source references are to the immutable `main.tex` snapshot.

## Scope and path certificate

The recursion clause (851–871) requires the intermediate word V to contain
only north and diagonal steps. The stronger coloring statements (2473–2535)
use a geometric single-bounce hypothesis without explicitly restricting V.
Start with the recurrence-facing scope. A local word pattern alone is not
a sufficient bounce hypothesis.

Let s be north for case I and diagonal for case II. Set

    R = U ++ [s, north] ++ V
    p = endpointFrom 0 0 R = (i,j)
    r = endpointFrom 0 0 (U ++ [s])

Require validity of `R ++ [diagonal,east] ++ W`, no east step in V,
`r.2 = i+1`, and `i+1 < j`. The bounce begins at `(i+1,j+1)` and returns west
at height `i+1` to the point after s, incident to the following north step.
Monotonicity and the no-east condition certify the single return; formalizing
that geometric correspondence is a separate obligation if a general bounce
procedure is later introduced. See the bounce definition at 665–692.

The successor words are

    QI  = U ++ [north,north] ++ V ++ [east,diagonal] ++ W
    QII = U ++ [north,diagonal] ++ V ++ [east,diagonal] ++ W.

First prove their validity. The final diagonal/east swap needs `i+1 < j`;
the initial diagonal/north swap in II preserves validity directly.

## Planned graph obligations

Put y=i+1 and z=j. Validity gives finite vertices i<y<z. In case I prove

    normal(P) = insert (y,z) normal(QI)
    strict(P) = insert (i,z) (strict(QI).erase (y,z)).

In case II, put a=(endpointFrom 0 0 U).1; the return condition gives the
prefix endpoint `(a,i)`. Prove

    normal(P) = insert (y,z) (normal(QII).erase (a,i))
    strict(P) = insert (a,i) (insert (i,z)
      ((strict(QII).erase (a,i+1)).erase (y,z))).

These are candidate scanner identities to prove, with membership/freshness
facts exposed explicitly. Do not use them as assumptions in a theorem claimed
to complete the paper's path relation.

## Coloring layer

The checked `ColoringSwap.lean` implements the source swap (2422–2433) and
proves involutivity and monomial preservation. It makes no claim about
admissibility or ascents without graph hypotheses.

A useful isolated next lemma is the restricted swap-sum identity on any path
whose strict edges are invariant under swapping i,y and whose normal edges,
after erasing (i,y), are invariant under that swap. Prove the remaining ascent
contribution changes by exactly one. The path-scanner work must later prove
these graph hypotheses in each use. This models Lemma `swapMap` (2436–2467).

Case I then partitions colorings by comparisons at i,y,z, using the identity
map or the swap, to prove `G_P = C(q) * G_QI` (2473–2519). Case II partitions
by the two changed constraints: one identical class, one empty by transitivity,
and two swapped classes with equal ascent count (2523–2658). It yields
`G_P = G_QII`. Keep these finite-sum proofs independent of the recursive
invariant and of the unresolved general bounce/termination arguments.
