# Crossing-corner slides and their smaller-area corrections

Status: audited mathematical proofs, not Lean declarations. These results
continue [strict-chain normalization](COMPONENT_CHAIN_NORMALIZATION.md).
They give actual moves between representatives and an exact signed identity
for both valuations. Reconstruction into whole smaller components remains open.

## Geometry of the available slots

We use an ordinary interval-closed natural graph G and any set S of strict
corners. Its strict chains include singleton vertices. An anchor is a selected
normal set whose edges increase the chain maximum r. Fix distinct chains A,B
with r(A)<r(B), and merge their vertices in the original order.

A natural normal edge a→b from A to B must occupy consecutive positions AB
in this merged list. An intervening A vertex would give a strict A edge
properly contained in ab; an intervening B vertex would give a strict B edge
properly contained in ab. Either contradicts corner maximality.

Conversely, an AB adjacency is natural if a has an A-successor or b has a
B-predecessor: the corresponding strict corner contains ab and interval
closure supplies it. The only possible exception has a terminal in A and b
initial in B. It is the unique possible bridge when all A vertices precede
all B vertices, and exists precisely when ab belongs to G. Saturation alone
does not force this bridge.

Between two consecutive AB slots, the merged word is exactly ABAB. Indeed,
an intervening AA pair bracketed by B vertices would be a strict A corner
properly inside a strict B corner; an intervening BB pair bracketed by A
vertices gives the reverse contradiction. Thus successive slots are

    (a,b), (c,d),     a<b<c<d,     ac,bd∈S.

If there is more than one slot, they are all natural. This description does
not depend on either chain beginning first. Being an anchor edge is different
from being rotatable in the normalization fiber: ab is rotatable only when
b has a strict predecessor lying before a.

## Exact cover and mixed-cycle tests for a slide

Fix crossing corners ac,bd as above, with r(a)=r(c)<r(b)=r(d). Let Q be an
anchor exterior omitting ab and cd. It also omits bc, which decreases chain
maxima. Include S in each state implicitly. Consider

    Q+ab  →  Q+bc  →  Q+cd.

This is a path of two ACTUAL ordinary flips if and only if Q has neither
an all-normal path a→b nor an all-normal path c→d.

For the first flip, ac is a cover: any alternate path lies inside that
strict corner, is all-normal, and cannot return from B to A in increasing
chain-max order. The short ab is a cover exactly when Q has no path a→b.
For the second flip, the short bc is a cover because an alternate path would
be all-normal in Q and decrease chain maxima. An alternate path for long bd
must start with bc and continue along a Q-path c→d: without bc it would be
an all-normal path within one strict chain. This proves the asserted tests.
We use the usual equivalent source-cover criterion for the target covers.

The middle state is mixed-acyclic if and only if the mixed graph of Q∪S
has no path c→b. The exterior is an anchor and hence mixed-acyclic; adding
bc creates a cycle exactly under that reachability condition. This test can
be stricter than the two ordinary cover tests.

For a precise diagnostic, use one-based vertices, areas (0,1,2,3,3,3),
S={14,25,36}, and Q={23,45}. The chain maxima are 4<5<6. Both ordinary
flips 13→34→46 are valid, but the middle mixed graph has the cycle
3→4→5→2→3. The endpoints are anchors. This diagnoses why genuine component
connections cannot be discarded merely because an intermediate state has
zero alternating contribution.

## Consecutive chains give unconditional slides

Suppose A and B are consecutive in the order of ALL strict-chain maxima,
including singleton chains. Then the above slide is always actual and
mixed-acyclic, for arbitrary anchor exterior Q omitting ab and cd.

Every mixed path from c to b has nondecreasing chain maxima. With no chain
between A and B, it would cross exactly once by a normal u→v from A to B.
Before crossing it can only move backward in A, so u≤c; afterwards it can
only move backward in B, so v≥b. Corner maximality forces u∈{a,c} and
v∈{b,d}. For example u<a would make uv properly contain the next A corner;
v>d would make it properly contain the previous B corner. The natural order
and maximality exclude cb and ad. The only possible crossing edges are ab
and cd, both absent. Hence no such mixed path exists.

The two all-normal bypasses are also impossible: increasing chain maxima
would require a single A-to-B edge, namely the missing ab or cd. Thus the
ordinary cover tests hold as well. Chains outside this pair may carry
arbitrary anchor edges; they cannot intervene and return in chain-max order.

Consequently, with all other anchor edges fixed, any two selections of the
same number k of A-to-B slots lie in the same entire source component.
Consecutive occupied/empty slots can be exchanged by the slides above, so
ordinary adjacent swaps take every selection to the first k slots. Each
swap is realized by two actual flips with mixed-acyclic intermediate state.
For zero or one available slot the assertion is immediate. This proves
connectivity of these selections, not that they exhaust a whole component.

## An exact signed semantic slide

Let X be K or E and R_X(Q)=∂_S X(Q∪S). Retain the notation of the
[residual diamonds](COMPONENT_HRV_DIFFERENCES.md#residual-diamonds-and-a-reconstruction-obstruction).
For a strict corner f with normal shorts u,v, define

    Φ_f^X(Q;u,v) = Σ_(J⊆S\{f}) (−1)^|(S\{f})\J|
      · [X(Q+J+u+v)−X(Q+J+u)−X(Q+J+v)+X(Q+J)].

Its four states lie in the actual smaller diagram (G\{f},S\{f}), or in
further corner deletions. The shorts remain normal. The two strict-long
diamonds give

    R_X(Q+ab)+R_X(Q+bc) = R_X(Q)+Φ_ac^X(Q;ab,bc),
    R_X(Q+bc)+R_X(Q+cd) = R_X(Q)+Φ_bd^X(Q;bc,cd).

Subtracting cancels both the middle contribution and the term with fewer
normal edges. We obtain the same signed slide formula for BOTH valuations:

    R_X(Q+ab)−R_X(Q+cd)
      = Φ_ac^X(Q;ab,bc)−Φ_bd^X(Q;bc,cd).

Every term on the right has strictly smaller half-square area. This identity
holds even when the slide fails the cover tests or its middle is mixed-cyclic;
consecutive chains are needed only for the unconditional flip interpretation.
It can also be summed along any of the packing paths above, expressing the
difference of endpoint residuals by an explicit signed smaller-area sum.

These are state sums, not yet sums of whole smaller components. Smaller-area
induction does not make either correction vanish pointwise. In particular,
the identity is not an equality of residuals along slides, nor an identity
for the normalization fibers. Under the consecutive-chain hypotheses there
is an exact obstruction to applying component induction to either correction
by itself. In G\{ac}, retain all
other strict corners and compare Q+bc with Q+cd. The correction Φ_ac gives
them coefficients −1 and 0 respectively, although they are actual flip
neighbors via the remaining strict long bd. Deleting ac does not affect this
flip. Likewise Φ_bd gives unequal coefficients along the surviving ac flip
in the other deletion diagram. The two corrections belong to different
diagrams, so merely subtracting them does not fix either mismatch.

To finish the author's induction we must show
that the correction multiplicities, after collecting all states of the
chosen component and any auxiliary recurrence rows, are constant on every
smaller component. Normal-long flips and connections through mixed-cyclic
states remain part of that obligation.

The [mixed-closure companion](COMPONENT_MIXED_CLOSURE.md) supplies further
common semantic zero relations: a normal edge already implied by the mixed
order can be inserted or removed in the alternating correction. These give
additional redistribution freedom; component reconstruction remains open.

Primary audited the slot and cover arguments and the signed subtraction.
Terra reviewed the two-chain geometry; Astra independently derived the cover
criteria, consecutive-chain lemma and signed identity. No enumeration,
compilation, reference edit or Overleaf edit was needed.
