# Moving one outgoing edge in an ordinary unicyclic state

2026-09-28. We prove an actual-flip repair that changes one outgoing
edge and fixes every other selected edge. The theorem applies to any
ordinary interval-closed diagram; it does not need NN eligibility,
saturation, or a strict retained long edge. Primary and Astra independently
audited the local proof and all cover tests. Its application to
[first mixed NN joins](COMPONENT_LEFTMOST_NN_UNICYCLIC.md) is given below.

## Statement and strategy

Let G be an ordinary interval-closed natural graph, with any allowed
set of strict corners. Selected edges point forward in the vertex order.
Write a<b=a+1<d<c and put f=ac, r=bc, q=ab.

**Theorem.** Let B be a connected unicyclic selected state containing
f,r,ad and omitting q,bd. Then B and B−ad+bd belong to the same actual
flip component. The path retains f,r and fixes every other selected
edge at its endpoints.

We separate the case where ad is a bridge from the case where it lies
on the unique cycle. Every exchanged edge lies properly inside f,
so it is natural and cannot be a strict corner. An attached component
meeting the displayed part in one vertex cannot alter its cover tests:
a simple path cannot enter that component and return to the same vertex.
Thus all other selected and strict edges may be retained.

## When ad is a bridge

If f and r both cover, use

    ad → dc, retaining f;
    dc → bd, retaining r.

These moves transfer the component attached by ad from a to b. This
attached component may contain the unique cycle; the two bridge moves
are still actual and do not change the cover status of f or r.

Otherwise exactly one of f,r is redundant. The unique cycle contains
that edge and its directed bypass. The other edge is a bridge:
a bypass of f cannot visit b, since a,b are adjacent and q is absent;
a bypass of r cannot visit a. The component attached by ad is now a
tree and contains no bypass vertex.

Suppose first that f is redundant. Write its bypass as

    a→x₀→x₁→...→xₖ=c,       b<x₀.

For i=k−1,...,0, replace xᵢxᵢ₊₁ by bxᵢ, retaining bxᵢ₊₁.
The first retained edge is r. The first move breaks the bypass of f;
afterwards every edge of the remaining cycle covers. We reach the
four-cycle {f,r,ax₀,bx₀}, with the other bypass vertices attached at b.
If r was redundant instead, sweep its bypass in the same way using
a in place of b and initially retaining f. This reaches the same
kind of four-cycle. Both sweeps stay inside f and retain every exterior
edge; no tree normalization or NN symmetry is involved.

At the four-cycle all core edges cover. Transfer the tree attached
by ad from a to b by the two displayed flips, then undo the sweep.
The transferred tree is attached only at b and does not affect the
reversed cover tests. Every other edge returns to its original position,
proving the bridge case.

## When ad lies on the unique cycle

First note that r covers. A directed bypass of r lies entirely in
[b,c], so its cycle cannot contain ad, whose tail is a<b. Such a
bypass would give a second cycle. We now treat the remaining cases.

**Case 1: f is redundant.** Its unique bypass must start with ad.
Write the rest as

    a → d=x₀ → x₁ → ... → xₖ=c.

All edges on this path are normal, and b<d<c. Starting from the end,
for i=k−1,...,0 make the flip

    xᵢxᵢ₊₁ → bxᵢ, retaining bxᵢ₊₁.

The initial retained edge is r=bc. It is a bridge and covers; every
path edge covers since f is the sole redundant edge. The first move
breaks the bypass of f. After each subsequent move, the cycle consists
of f,r,ad, the initial part of the old path, and the current edge
from b. All these cycle edges cover. Thus the whole backward sweep
is actual.

We reach the four-cycle {f,r,ad,bd}, with each intermediate xᵢ,
1≤i<k, attached to b by bxᵢ. Transfer each of these pendant trees
from b to a by two flips through c. Then, for i=0,...,k−1, make

    axᵢ → xᵢxᵢ₊₁, retaining axᵢ₊₁.

This restores the old path and removes ad, while keeping bd. During
this forward sweep the unprocessed arms cover. Only the final state
makes r redundant, through bd and the restored path; r is not used
after that step. This proves the required transfer in Case 1.

**Case 2: ad is redundant.** Its bypass starts a→x with b<x<d,
since q is absent and the direct edge ad is excluded from its bypass.
The edges f,r are bridges. Use

| Retained edge | Exchanged edges |
| --- | --- |
| f | ax → xc |
| f | ad → dc |
| r | dc → bd |
| f | xc → ax |

The first move breaks the bypass of ad. After the second, xc is the
only redundant edge, through the remainder of that bypass followed by
dc. The third move breaks its bypass, so xc covers when used in the
last move. All other required edges cover. The original bypass and
all exterior edges are restored, while ad has become bd.

**Case 3: f and ad both cover.** The move ad→dc, retaining f,
is actual. If r still covers afterwards, finish with dc→bd,
retaining r.

Suppose instead that this first move makes r redundant. Its new bypass
must use dc, since r covered before the move. Thus the original state
contains a directed path

    b → x → ... → d,       b<x<d.

The inequality x<d uses the absence of bd. This path together with
ad,f,r is already the unique cycle, and all its edges cover. Replace
the attempted two-move path by

| Retained edge | Exchanged edges |
| --- | --- |
| r | bx → xc |
| f | ad → dc |
| r | dc → bd |
| r | xc → bx |

After the second move, only xc is redundant. After the last move,
only bd is redundant. Neither is required to cover at those times.
The intermediate cycle edges otherwise cover, and the table restores
the original b-to-d path. These cases exhaust the possibilities and
prove the theorem.

## What this resolves in the first mixed join

We now impose the eligible NN hypotheses from
[the packet theorem](COMPONENT_RECURRENCE_REDUCTION.md), with strict f
and adjacent swap σ=(a b). For a right target flip, put Q=T∪{ad,bd} and P=T∪{ad}. The first
mixed source join compares

    S₀∪σT∪{f,ad,bd},       S₀∪T∪{f,ad,r}.

The first state flips bd→q, retaining ad. Its middle partner is
M=S₀∪σT∪{f,ad,r}. Whenever the previously proved full swap applies
to M, we reach

    σM=S₀∪T∪{f,bd,r}.

The theorem, used backwards, now connects σM to the desired second
endpoint. Thus the held outgoing edge is no longer an additional
obstruction. The middle join and the applicability of the full swap
are separate obligations; neither follows from this theorem.

## An incoming edge need not admit the same transfer

We cannot replace the outgoing edge ad by an arbitrary incoming edge
ta in the theorem. Take area (0,1,2,3,4,5,6,4,5), strict corners
06,38, and the eligible NN step a=3,b=4,c=8. Consider

    A={06,02,26,13,38,48,68,35,78},
    B={06,02,26,14,38,48,68,35,78}.

These states are connected unicycles, contain f,r, omit q, and differ
only by the incoming bridge 13 versus 14. Deleting 06 gives trees
with respective maximal envelope intervals

    {02,13,26,38},       {02,14,26,38}.

In both, the maximal chain 0→2→6 forces a bypass of 06 in every tree
of that envelope. The
[whole-component insertion theorem](COMPONENT_TREE_CONNECTIVITY.md)
therefore identifies each source component with its respective whole
tree component. Their different envelopes prove that A and B are in
different source components. Both are inactive at 06. This is a
structural counterexample, not a failure of the component HRV formula.

## Verification

The original NN specialization passes exact actual-component checks in all 76
eligible NN instances through six vertices: 555 transfers, including
371 whose moved edge lies on the cycle. The two seven-vertex fixtures
area0123434 and area0123343 give 224 and 66 transfers, including 128
and 46 on-cycle cases. The two four-flip tables and the backward/forward
sweeps also pass direct cover checks; sweep lengths range from two to
22 flips. The nine-vertex incoming example is checked by its two tree
envelopes and the forced-chain theorem, without enumerating that whole
state space.

Related Rust: external `nn_component_transport.rs`, mode `--audit-right-arm`,
and `right_arm_paths.rs`, reusing the existing cover/flip and component model.
Frozen sources, commands, receipts and hashes are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/leaf-envelope/`.
No maintained Rust source, Lean build or manuscript change is involved.

The stronger statement is also checked on all ordinary natural graphs
through seven vertices, for every connected unicyclic selection and every
selected retained f, whether or not f is maximal or strict. This includes
unsaturated envelopes and diagrams without an eligible NN step. The
consumer checks endpoint membership in the entire actual component.
Related Rust: external `adjacent_transfer_general.rs`; frozen source,
commands and final receipts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/adjacent-transfer/`.

## Arbitrary-exterior transfer with two covering anchors

2026-09-29 continuation. The following construction is independent of the
unicyclic argument above. We retain all exterior edges and allow arbitrary
cycle rank. We do not claim that the earlier independent audit covers this
new argument.

Let u,v be distinct vertices, both less than d<c. Suppose a selected state B
contains uc,vc,ud, omits vd, and both anchors uc,vc cover. Their cover tests
imply that neither root reaches the other. There is no selected d-to-c path.
Neither adjacency of the roots nor maximality of the anchors is required.

**Covering-arm lemma.** If ud also covers, then

    B ~ B-ud+vd.                                      (A1)

Both anchors still cover at the endpoint. All other edges are restored.

Put P=B-ud, and list in increasing order

    J={y : v<y<d, vy is selected in P, y reaches d in P}.

First exchange vy for yc, retaining vc, for each y in J. The edge vy
covers when processed: a bypass starts with an earlier outgoing edge vz
with z<y and z reaching d, which has already been removed. Added edges end
at c and cannot supply that bypass. Each exchange preserves the cover of
vc. It preserves the cover of uc as well: a new bypass through yc would
give an original u-to-y-to-d path in P, contrary to the cover of ud.

The sweep removes every v-to-d path; new edges end above d. It leaves ud
a cover and does not create a d-to-c path. We can now perform

    ud -> dc [retain uc],
    dc -> vd [retain vc].                            (A2)

For the first flip, uc and ud cover and dc is absent. The second retained
anchor vc covers after the first flip because the sweep cleared all
v-to-d paths. The edge dc covers, and vd is absent, so the second flip
is actual too.

Undo the J-sweep in reverse order. Relative to the corresponding forward
state, ud is removed and vd is added. The latter cannot bypass a tested vy,
whose head y is below d, or a tested yc, whose tail y is above v. It cannot
bypass vc because there is no d-to-c path. Every inverse flip is actual.
The other anchor uc still covers: a new bypass using vd would require
u to reach v, which was excluded at the outset and was not changed below c.
This gives 2|J|+2 moves and proves (A1).

**Outgoing-cut extension.** We may drop the cover assumption on ud under
the following explicit condition. With P=B-ud, let

    I={y : u<y<d, uy is selected in P, y reaches d in P}.

Assume v does not reach any y in I. Then (A1) still holds.

Process I increasingly, replacing uy by yc while retaining uc. The same
first-edge argument makes each uy a cover. The condition on v means that
these additions cannot bypass vc, so both anchors remain covers. The sweep
clears every u-to-d path except ud. Apply the covering-arm lemma to this
prepared state, then undo the I-sweep.

During restoration, the added vd cannot bypass a tested uy, whose head is
below d, or a tested yc: such a bypass would require a d-to-c suffix,
which remains absent. It cannot bypass uc for the same reason. Thus all
inverse flips are actual. This construction has

    2|I| + 2|J_prepared| + 2

moves. Every exchanged edge lies properly inside one of the selected
natural anchors, so it is natural and cannot be a strict corner. The proof
therefore includes arbitrary exterior edges and strict decorations.

The condition is automatic when ud covers, since I is empty. It is not
automatic for a redundant arm. For example, the selected relation
{04,14,02,12,23,03}, with roots 0,1 and arm 03, has 2 in I and 1 reaches 2.
An exact eight-flip path transfers 03 to 13 in this particular example,
but the construction above does not prove the general shared-branch case.
It also does not assert a transfer with redundant anchors.

### Verification of the new construction

Related Rust: the existing external `first_join_tree_lifts.rs`, function
`two_anchor_path` and option `--two-anchor-check`, uses the established
`component_source_probe::{cover,flip}` oracle. In the fixed complete
six-vertex natural diagram, with 05 strict, it checks every ordered choice
of the two roots and d<c and every state satisfying the stated hypotheses.
All 5032 covering-arm and 296 redundant-arm instances pass, comprising
11888 actual flips and exact endpoint/strict-edge checks. There are 222
instances outside the outgoing-cut hypothesis; these are not failures.
This is one fixed small diagram, not a scan over diagram families.

The separate `--two-anchor-probe` compares whole-component membership only
at roots 0,1, c=5 in that same diagram. All 411 covering-arm and 106
redundant-arm comparisons pass. That finite evidence does not remove the
condition in the theorem. It also records the eight-flip example above.

Frozen sources, commands and logs are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/two-anchor-transfer-20260929/`.
No Lean/Lake build, new reviewer, worker or maintained Rust change was used.
