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

For case I, the return condition simplifies to
`(endpointFrom 0 0 U).2 = (endpointFrom 0 0 R).1`. Terra separately audited
this exact planned theorem interface, including the successor's validity gap.

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

For case I the correct common background is the valid word
`B = R ++ [east,east,north] ++ W`. The inserted north is essential: replacing
`[diagonal,east]` by `[east,east]` alone would end one unit too low. The planned
local equations are `normal(P)=insert(y,z) normal(B)`,
`strict(P)=insert(i,z) strict(B)`, `normal(QI)=normal(B)`, and
`strict(QI)=insert(y,z) strict(B)`. The strict edges of B should be swap
invariant; its normal edges with `(i,y)` erased should also be swap invariant.
These remain source-geometry obligations, not assumptions of the target
path theorem.

## Coloring layer

The checked `ColoringSwap.lean` implements the source swap (2422–2433) and
proves involutivity and monomial preservation. It makes no claim about
admissibility or ascents without graph hypotheses.

The checked `SwapSum.lean` proves the restricted swap-sum identity on any path
whose strict edges are invariant under swapping i,y and whose normal edges,
after erasing the normal edge (i,y), are invariant under that swap. Its proof
shows the remaining ascent contribution changes by exactly one. The path-scanner work must prove
these graph hypotheses in each use. This models Lemma `swapMap` (2436–2467).

`PrefixScanners.lean` proves unconditional endpoint and scanner append laws.
`BouncePath.lean` proves validity of `diagonal,north → north,diagonal` and,
under the endpoint gap, `diagonal,east → east,diagonal`; it provides their
valid-path constructors. These are geometry helpers, not bounce identities.
`SecondBouncePath.lean` proves the initial swap preserves its prefix endpoint
and constructs `secondBounceSuccessor` by composing the two valid swaps.

Case I then partitions colorings by comparisons at i,y,z, using the identity
map or the swap, to prove `G_P = C(q) * G_QI` (2473–2519). Case II partitions
by the two changed constraints: one identical class, one empty by transitivity,
and two swapped classes with equal ascent count (2523–2658). It yields
`G_P = G_QII`. Keep these finite-sum proofs independent of the recursive
invariant and of the unresolved general bounce/termination arguments.

For case I, primary also supplied Aristotle this finite bijection outline:
leave a coloring fixed when both colors at i,y are below the color at z;
otherwise swap the colors at i,y. Since z is distinct from i,y, this is an
involution. The graph equations above and the checked swap-weight lemma
should give `weight(P,c) = C(q) * weight(QI,T(c))` in every case. The remote
request must prove the graph equations from word hypotheses, so its final
target is the full recurrence-facing first-bounce identity.

## Direct second-bounce coloring switch

Primary proposed and Terra independently checked the following more explicit
II proof. This remains a proof plan until its scanner and weight statements
are checked in Lean.

Use `B = U ++ [east,north,north] ++ V ++ [east,east,north] ++ W`. Both local
replacements preserve displacement. Write N and S for its normal and strict
edges. The planned equations are

    normal(P) = insert (y,z) N
    strict(P) = insert (a,i) (insert (i,z) S)
    normal(QII) = insert (a,i) N
    strict(QII) = insert (a,y) (insert (y,z) S).

The two inserted normal edges are fresh. Also `(i,y) ∈ N`; S and
`N.erase(i,y)` are swap invariant. The path hypotheses imply `a<i<y<z`,
including finiteness of all four vertices. The initial diagonal supplies
`a<i`; the final gap supplies `y<z`.

Set `A=c a`, `I=c i`, `Y=c y`, `Z=c z`. Leave c fixed when both I and Y
lie strictly in `(A,Z)`; otherwise swap i,y. This is an involution because
a,z are fixed and the interval predicate is symmetric. Background strict
admissibility is preserved. For `A<I<Z`, there are three exhaustive cases:

- Both I,Y are in `(A,Z)`: use identity; each path gains one normal ascent.
- `Y≤A<I<Z`: swap; P gains one local ascent, Q gains none, and the background
  ascent count increases by one under the swap.
- `A<I<Z≤Y`: swap; P gains none, Q gains one, and the background ascent count
  decreases by one under the swap.

Equality at Y=A or Y=Z is included. If the source's local strict condition
fails, the transformed target's condition also fails; background
inadmissibility likewise makes both weights zero. This should prove
`weight(P,c)=weight(QII,T(c))` pointwise, then the second bounce sum identity.
No division or cancellation of q is needed.

## Implemented boundary

The first identity and all its graph hypotheses are now locally checked in
`BounceScanners.lean`, `FirstBounceGraph.lean`, `BounceWeight.lean`, and
`FirstBounce.lean`. The second plan above is the active Aristotle target;
its valid successor is already checked in `SecondBouncePath.lean`.
