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

## Why absence of a target path does not replace the anchor covers

2026-09-29 continuation. The following obstruction rules out a proposed
shortcut for the retained-edge DN comparison. It does not contradict the
two-cover theorem above or the retained-edge comparison itself.

Take the complete natural diagram on 0,1,2,3,4 with 04 strict, and set

    B = {02,03,04,12,14,24,34},
    B'= {02,04,12,13,14,24,34}.

Thus a=0, b=1, d=3, c=4; B contains ac,bc,ad, omits ab,bd, and has
no b-to-d path. The moved arm ad even covers. Nevertheless B and B'
belong to different actual components.

We prove separation without enumerating components. Delete 04 from B',
and let H be the interval envelope with maximal edges 02,14. Its edges are

    {01,02,12,13,14,23,24,34}.

Every state in the H-component of B'-04 selects its two maximal edges
02,14 and has six edges. Every such selection has a 0-to-4 path. If 01
is selected, use 01,14. Otherwise four of 12,13,23,24,34 are selected.
If 24 is present, use 02,24; if not, both 23 and 34 are present, giving
02,23,34. Inserting 04 therefore makes it redundant throughout this
whole H-component. Insertion preserves reachability and all other cover
tests. The inserted corner cannot be retained by an actual flip, and any
other retained edge has both shorts in H. Consequently the inserted family
is a whole component in the original complete diagram. None of its states
selects 03. Since B selects 03, it lies outside that component.

This does not merely compare two components inactive at 04. Starting from
B, the following four actual flips make 04 a cover:

    12 -> 01 [retain 02],
    01 -> 13 [retain 03],
    34 -> 23 [retain 24],
    24 -> 12 [retain 14].

Their endpoint is {02,03,04,12,13,14,23}. Here 04 is the only selected
edge ending at 4 from a vertex reachable from 0, so it covers. The
displayed source and retained edges cover at each step; this is also
verified by the external diagnostic.

Even retaining the cover assumption on bc alone is insufficient if the
moved arm may be redundant. Replace B by

    B0 = {02,03,04,14,23,24,34}.

Now 14 covers and 1 still does not reach 3. Replacing 03 by 13 again
gives a state in the closed six-edge H-family after deleting 04, whereas
B0 selects 03. The two flips 34->13 [retain 14] and 24->12 [retain 14]
connect B0 to the same 04-covering state above.

Thus neither absence of b-to-d reachability nor activity of the source
component at ac permits us to drop the proved anchor hypotheses. In the
retained-edge DN problem, we cannot simply transfer wt to xt, flip
xs to st, and transfer back. A direct repair must use the extra s-data.
This distinction already occurs in a genuine DN source. Shift the labels
of B up by one and adjoin the strict edge 01. With
(w,x,s,t,z)=(1,2,3,4,5), the source state is

    S={01,13,14,15,23,25,35,45}.

The attempted 14-to-24 transfer still changes its component: the added
edge 01 cannot take part in any flip or affect a cover test on 1,...,5.
But the desired retained-edge comparison 23-to-34 is valid, by the
previously proved four-flip row:

    23 -> 12 [retain 13],
    12 -> 24 [retain 14],
    45 -> 34 [retain 35],
    24 -> 45 [retain 25].

It restores every other edge, including 14. Thus the failed intermediate
transfer is not a counterexample to the required retained-edge theorem.
The [crossing-cover construction](COMPONENT_DN_RETAINED_EDGE.md#sliding-the-moving-edge-along-crossing-covers)
is one such repair, with separately stated hypotheses.

Related Rust: the external `first_join_tree_lifts.rs`, option
`--outgoing-no-path-probe`, reuses the established component oracle on one
fixed complete six-vertex diagram. Of 2336 no-path comparisons, 60 fail;
of 736 comparisons with a path, 152 fail. The displayed five-vertex
obstruction occurs with one isolated vertex inserted. Its components have
34 and 9 states, but those counts are not used in the separation proof.
In contrast, all 576 applicable retained-edge comparisons in that same
fixed diagram lie in one component pairwise. This is finite evidence for
the latter statement, not its arbitrary-exterior proof.
Receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/outgoing-no-path-20260929/`.

## Covers in the background and an absent direct suffix

2026-09-29 continuation. We can allow an anchor to become redundant after
adding the moving arm, provided both anchors cover before the arm is added.
The direct suffix must be absent; arbitrary longer suffix paths are allowed.

**Proposition.** Let u,v be distinct vertices with u,v<d<c. Let Q contain
covering uc,vc, have no u-to-d or v-to-d path, and omit dc. Then

    Q+ud ~ Q+vd.                                     (A3)

We include the full exterior in every cover test. Every edge except the
moving arm is restored, and all strict edges remain selected. In particular,
we do not assume that uc covers in Q+ud or vc covers in Q+vd.

The roots do not reach each other in Q: either such path would bypass
one of uc,vc. Adding an edge ending at d cannot change this fact. Put

    I={h : d<h<c, hc is selected in Q, d reaches h in Q},
    Q0=Q minus {hc : h in I}.

We prepare the two endpoints differently. From S=Q+ud, process h in I
in decreasing order, exchanging

    hc -> vh [retain vc].                            (A4)

The anchor vc covers in S, since v cannot reach u. The edge hc covers
at its turn: a bypass has final edge kc with k>h and d reaching k, so
that edge has already been removed. New edges start at v<d<h and cannot
be used by a path starting at h. The target vh was absent in Q, since
otherwise vc would not have covered. It has not been added at an earlier
step. Removing hc clears every h-to-c path, so adding vh preserves vc
covering. Each flip is actual.

Because dc is absent, the cut removes the last edge of EVERY d-to-c
path. It leaves the exact state

    S_v=Q0+ud+{vh : h in I}.                          (A5)

Both uc and vc cover there. The added ud has no d-to-c suffix, and u
cannot use the new vh since it does not reach v. Conversely, starting
at T=Q+vd, the symmetric cut hc->uh [retain uc] is actual and ends at

    T_u=Q0+vd+{uh : h in I},                          (A6)

again with both anchors covering. We retain the full second cut for
later reversal; it is not the same preparation as (A4).

Starting at S_v, process I in INCREASING order. For each h transfer vh
to uh by the covering-arm lemma (A1), with roots v,u and arm endpoint h.
At the start of this transfer, vh covers. Indeed, Q has no v-to-h path:
such a path followed by the original hc would bypass vc. Previously
transferred arms start at u, which v cannot reach. The remaining added
arms vk have k>=h; none with k>h can begin a bypass to h. The selected
ud starts at the inaccessible root u. These facts exclude every bypass
of vh. The target uh was absent in Q by the original cover of uc and
has not yet been inserted; h>d keeps it distinct from ud.

The lemma permits u already to reach h, for example through ud. It
clears the interfering outgoing paths as part of its construction and
restores all other edges. In particular, both anchors cover at the end
of each transfer. Thus we can apply it successively as stated.

We now have Q0+ud+{uh : h in I}. The edge ud still covers: Q has no
u-to-d path, and every added uh ends above d. Also vd is absent. Apply
(A1) once more, transferring ud to vd. The resulting state is EXACTLY
T_u. Reverse the recorded cut from T to T_u. Each inverse is actual
because we start at its exact endpoint, with every other edge restored.
We finish at T, proving (A3).

All exchanged shorts lie properly inside one of the natural longs uc,vc,
including those in the applications of (A1). They are therefore normal;
no original strict edge is exchanged. The proof allows arbitrary exterior,
nonadjacent roots and arbitrary cycle rank.

### Why the direct suffix is still a separate case

If dc is selected, extending I to include d makes both prepared endpoints
contain ud AND vd. A remaining vh can then be redundant through vd and
a d-to-h path. The increasing-order argument above no longer exposes the
moved arm. We have not proved (A3) with a selected redundant dc. A selected
covering dc is easier: dc->vd [retain vc], ud->dc [retain uc] is an actual
two-flip row, since removing that covering dc clears all d-to-c paths.

Related Rust: the external `first_join_tree_lifts.rs`, helper
`background_anchor_path` and option `--two-anchor-background-transfer`,
checks (A4), both prepared states, each use of (A1), and the exact reversal.
Two fixed n9/n12 states pass 16 and 32 flips. The latter has nonadjacent
roots; both have multiple suffix paths, initially redundant incoming
edges and shared exterior descendants outside those suffixes. No state
space is enumerated. A separate fixed selected-dc example on five vertices
has an eleven-flip path (71 states visited); this is evidence only for
that example. Sources and receipts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/retained-suffix-covers-20260929/`.
No Lean/Lake build, worker, consultant, maintained Rust edit or independent
review was used. Earlier text in this note remains a verbatim prefix.
