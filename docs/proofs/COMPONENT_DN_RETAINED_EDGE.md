# Carrying a retained-edge DN flip back to the source

2026-09-28--29. We prove three arbitrary-exterior cases of the retained-edge
calculation in [joint DN repairs](COMPONENT_DN_JOINT_REPAIRS.md).
The unrestricted statement remains open. These are statements about actual
source components; they do not assume the component HRV formula.

## The configuration

Let w<x<s<t<z, with x=w+1, and write

    f=wz, r=xz, A=wt, p=xs, j=st, g=xt, q=wx.

All these edges lie inside the natural strict corner f. Let Q be a selected
source relation containing f,r,A, with p,j,g,q absent. Include all other
strict edges and the full exterior in Q. Suppose Q has no directed path

    x -> s,   s -> t,   x -> t.                       (1)

These are exactly the reachability conditions for the target flip retaining
g and exchanging p,j, after we replace the source corners e,f by the target
corners e',r. Here e=uw and e'=ux, with u<w, as in the DN step.
The corner change cannot affect a path between x,s,t.
In particular, p covers in Q+p and j covers in Q+j.

We seek a path of actual source flips from Q+p to Q+j, restoring every
other selected edge. Such a path proves equality of their source component
labels, as required to carry this target flip through the recurrence.

## The three-flip repair with two covering edges

**Lemma.** Suppose there is a vertex y<s, distinct from x, such that
Q selects yz,yt and both yz and r cover in Q+p. Then Q+p and Q+j
belong to the same source component. The vertex y may lie on either side
of x; it need not be the original w.

First process in increasing order all selected yv, excluding ys,yt,
such that v reaches s or t. Replace yv by vz, retaining yz. The smallest
remaining such v makes yv a cover: a bypass would start with an earlier
outgoing edge already removed. The edge ys cannot start such a bypass,
since s cannot reach t. The cover of yz makes each exchange actual and
is preserved by it.

This also leaves r a cover. A new x-to-z bypass would use a new vz,
forcing x to reach s or t through v, contrary to (1). A path starting
with the selected xs would instead force s to reach t or itself.
There is no path from x to y: either y<x, or the selected yz and the
covering r exclude it. The sweep only deletes edges starting at y and
adds edges ending at z, so it creates no new path ending at s or t.

Now yt covers, and the only possible y-to-s path is the edge ys itself.
There is no s-to-z path because r covers with xs selected, and no
t-to-z path because yz covers with yt selected. If ys is absent, use

    xs -> sz [retain r],
    sz -> ys [retain yz],
    ys -> st [retain yt].

If ys is selected, use

    xs -> sz [retain r],
    ys -> st [retain yt],
    sz -> ys [retain yz].

The stated covers and absent paths make every flip actual. Both paths
replace p by j and preserve all other edges of the normalized relation.
Undo the outgoing exchanges in reverse order. Compared with each forward
state, p is deleted and j added. The new st cannot bypass yv, since v<t,
or bypass vz or yz, since there is no t-to-z path. Every reverse flip is
actual and restores the exterior. All exchanged edges lie properly inside
selected natural edges, so none is strict.

## When f covers

**Proposition.** If f is a cover in Q+p, then Q+p and Q+j belong to the
same complete source component. There is no further condition on the exterior.

We first make r a cover. Consider all selected vz other than f,r for which
x reaches v in Q+p. Process them in decreasing order of v, replacing vz
by wv while retaining f. The processed vz covers: a bypass would end at
uz with u>v reachable from x, which was already removed. The cover of f
excludes a path from w to v, so wv is absent and the exchange is actual.
It leaves f a cover.

Throughout this sweep, reachability from x to vertices below z is unchanged:
new edges start at w<x, and deleted edges end at z. Thus the same decreasing
list remains valid, and the resulting r covers. Conditions (1) persist.
The edge A stays selected, since f covering and A selected exclude a path
from t to z, so tz was not on the list. The edge ws may have been added.

Apply the preceding lemma with y=w. It replaces p by j and restores
all other edges of the relation after this incoming sweep.

Now undo the incoming sweep. Compared with each forward state, p is
removed and j added. The new st cannot bypass vz or f without a t-to-z
suffix. A bypass of wv using st would require a path from t to v.
But vz was selected in the original relation, which had no t-to-z path;
and none of our changes creates a path from t to a vertex below z.
Thus every reverse exchange remains actual. All exterior edges are
restored, proving the proposition.

## When r covers and t reaches z

**Proposition.** Suppose r covers in Q+p and Q has a selected path from
t to z. Then Q+p and Q+j belong to the same complete source component.
In this case f is redundant through A and that path.

Choose a saturated selected path

    t=v_0 < v_1 < ... < v_m=z.

Starting with the covering edge r=xv_m, for i=m-1,...,0 exchange
v_i v_{i+1} for xv_i, retaining xv_{i+1}. Each flip is actual: the
current long edge covers, the selected path edge covers, and an existing
path from x to v_i would contradict the cover of the current long.
The newly selected xv_i covers and supplies the retained edge for the
next step. Earlier changes cannot spoil a path-edge cover, since their
added edges start at x<t and their other changes are deletions.

We have now selected g=xt as a cover. The edge p still covers, since every
new edge xv_i ends at or after t>s. Conditions (1) also leave no s-to-t
path. We can therefore exchange p for j, retaining g.

Undo the path exchanges in reverse order. A new bypass of a tested long
xv_i using st would require an x-to-s path. There is no such path after
we delete p: it was absent in Q and the preparation only added edges from
x to vertices at or above t. A tested path edge starts at or above t, so
its cover cannot be affected by st. All reverse exchanges are actual,
and restore every path edge. This proves the proposition.

## Two orders for the incoming sweep

**Proposition.** Suppose r covers in Q+p, Q has no path from t to z,
and one of the following holds:

- Q has no path from w to s;
- ws is selected, and ws and wt both cover in Q+p.

Then Q+p and Q+j belong to the same complete source component.

In the first case, exchange xs for sz, retaining r. This is actual because r and xs
cover. The new sz covers and r still covers. Since q is absent and w,x
are adjacent, w cannot reach x; the change therefore does not affect
reachability from w to any vertex below z.

For every selected vz, other than f,r, with v reachable from w, replace
vz by xv while retaining r, in decreasing order of v. Here v>x: q is
absent, and there is no vertex between w and x. The processed vz covers,
since a bypass would end at an already removed uz with u>v reachable
from w. The covering r excludes a path from x to v, so each exchange
is actual and leaves r a cover. Reachability from w below z remains
unchanged, because new edges start at the unreachable vertex x.

This sweep makes f a cover. It preserves sz, since w cannot reach s,
and preserves wt. The edge sz still covers: it had no bypass before
the sweep, and new edges starting at x<s cannot create one.
We can now exchange sz for ws, retaining f.

The resulting relation selects f,wt,ws, with f covering and no s-to-t
path. Apply the proved outgoing-sweep lemma in the joint DN note to
exchange ws for st, restoring every other edge of this relation.

Finally undo the incoming sweep. Relative to each forward state, sz has
been deleted and st added. A new bypass of r or a tested vz would need
a t-to-z suffix, which does not exist. A new bypass of xv using st would
need t to reach v; this too is impossible, because vz was selected in
the original relation, which had no t-to-z path. None of the preparatory
changes creates a path from t to a vertex below z. All reverse flips
are therefore actual, restoring the exterior and leaving exactly Q+j.

In the second case, first exchange ws for st, retaining wt, and then
exchange xs for sz, retaining r. The first move preserves the cover of r:
a new bypass would use st and require the absent t-to-z suffix. Removing
the covering ws also removes every w-to-s path. We can therefore perform
the same incoming sweep, retaining r, until f covers; the temporary sz
is preserved. Exchange sz for ws, retaining f, to restore the original ws.

Now undo the incoming sweep. Compared with each forward state, sz has
been removed and ws added. Every tested edge r,xv,vz starts at or above
x, whereas ws starts at w<x; it cannot create a bypass of any tested edge.
Thus reversal restores the full exterior and leaves Q+j. In this case
the desired st was selected before the incoming sweep, so no final
wt-retained flip is needed.

## Verification and scope

The existing independent Astra reviewer passed the three constructions, including
the sweeps, path preparation, central flips and restoration with arbitrary
exterior. Every exchanged edge is normal inside the designated source corner.

Related Rust: `first_join_tree_lifts.rs --retained-exterior` reuses the
existing exact source component and cover-flip functions. It checks all
eligible target flips in source areas 011234 and 0112345: respectively
8 and 576 pairs, all with identical source component labels. The latter
fixture has 16,384 source orientations and 1,471 complete components.
This is finite evidence for the remaining cases, not their proof.

Receipts are under the external `dn-outer-sweep/` directory. No Lean source
or build is involved. Cases not covered by the three propositions, the
left-hand retained-e' case, and complete component reassembly remain open.

## Recovery continuation: preparing a different covering triangle

2026-09-29. We preserve the preceding pre-crash text. The results below
extend its list of sufficient hypotheses; they do not settle the unrestricted
retained-edge statement. We write S=Q+p and T=Q+j, with the configuration
and the three forbidden paths in (1). A path may have arbitrary selected
exterior edges. All new flips occur inside the natural strict corner f.

### Bringing a path on the right to z

**Proposition.** Suppose r covers in S. Suppose s<y<t, yz is selected
and covers in S, and there is a selected path from y to t. Then S and T
belong to the same source component.

We choose a saturated path y=v_0<v_1<...<v_m=t. Starting with yz,
perform the following flips in increasing order of i:

    v_i v_(i+1) -> v_(i+1) z [retain v_i z].          (2)

The current long edge covers. Its selected path short covers because the
path is saturated and earlier changes only deleted path edges and added
edges ending at z. There is no alternative v_(i+1)-to-z path: together
with the selected path short, it would bypass the current long edge.
There is no alternative v_i-to-v_(i+1) path after deleting that short.
Thus each flip is actual and its new short supplies the next covering long.

The cover of r persists. Before the preparation, x cannot reach a path
vertex v_i: the remaining path to t would contradict (1), even in S,
since s cannot reach t. Adding edges ending at z does not change this
reachability below z. No new bypass of r can therefore use an added edge.
We have obtained tz selected and covering. The earlier proposition for
covering r and a t-to-z path now replaces p by j, restoring this entire
prepared exterior.

We undo (2) in reverse order. Every tested edge starts at or after y>s.
The new st cannot bypass any of them, and deleting xs cannot spoil a cover.
Every reverse flip is actual and restores the original path. This proves
the proposition. The case of a one-edge y-to-t path uses five flips in total.

### A selected branch between x and s

**Proposition.** Suppose x<y<s, r covers in S, and there is no t-to-z
path. Suppose wy,ys,yz,wt are selected covers in S. Finally, suppose
there is no w-to-s path after removing wy and ws from S. The edge ws may
be selected or absent. Then S and T belong to the same source component.

We use the following two local rows. In each row all unmentioned edges
remain selected or absent as before.

| Initial ws | Successive exchanges | Retained edges |
| --- | --- | --- |
| absent | wy to yt; xs to sz; ys to st; yt to wy; sz to ys | wt, r, yt, wt, yz |
| selected | wy to yt; ys to wy; xs to sz; yt to tz; tz to st; sz to ys | wt, ws, r, yz, sz, yz |

We verify the covers with the exterior present. Initially yt is absent,
and y cannot reach t, since wy and wt are selected and wt covers.
Likewise s cannot reach z, since ys and yz are selected and yz covers.
The cover of r excludes an x-to-y path. We first exchange wy for yt,
retaining wt. Both selected edges cover, and the two forbidden alternative
short paths show that this flip is actual. It preserves r and yz as covers:
a new bypass would need either x to reach y or a t-to-z suffix.

If ws is absent, removing wy removes every w-to-s path. Exchange xs
for sz, retaining r. The edge yt covers and ys still covers, so we can
exchange ys for st, retaining yt. After removing ys, y cannot reach s;
a new bypass of yt through st is therefore impossible. There is also
no w-to-s path, so the new st cannot bypass wt. We can exchange yt back
for wy, retaining wt. Finally exchange sz for ys, retaining yz. Both
shorts cover because s has no alternative path to z and y has no
alternative path to s. The final relation is T.

If ws is selected, it becomes a cover when wy is removed, by the final
hypothesis. Exchange ys for wy, retaining ws. The required covers follow
from the original covers of ys and wy; after this exchange y cannot reach
s. Now exchange xs for sz, retaining r. The edge yz still covers, since
y cannot reach s or reach z through t. Exchange yt for tz, retaining yz;
then exchange tz for st, retaining sz. The latter long covers because s
had no alternative path to z and could not reach t. Finally exchange sz
for ys, retaining yz. The deleted yt and tz no longer give a bypass of
yz, and the new st has no t-to-z suffix. This restores wy,ys,ws and all
other exterior edges, leaving exactly T. This proves the proposition.

The two rows explain why blindly reversing the preparation wy to yt is
insufficient: while ys and st are both selected, yt is redundant. The
order of the last exchanges removes that obstruction before restoration.

## Recovery continuation: both original anchors may be redundant

We give three further arbitrary-exterior sufficient conditions. For an
edge h, a cover statement in S-h is a statement about the full relation
after removing h, not just the displayed five vertices. Put b=sz and c=tz.
The hypotheses of the configuration, including (1), remain in force.

### A three-flip row

**Proposition.** Suppose ws and b are selected, wt and b cover in S,
f covers in S-ws, and r covers in S-p. Then S and T are connected by

    ws -> st [retain wt],
    sz -> ws [retain f],
    xs -> sz [retain r].                             (3)

Both f and r are redundant in S, through ws,b and p,b respectively.
Since f covers in S-ws and wt is selected, there is no t-to-z path.
The same f-cover condition, with b selected, rules out every w-to-s
path other than ws. Thus ws covers and the first flip is actual by (1).
It exposes f; adding st cannot create a bypass without a t-to-z suffix.
The edge b still covers, so the second flip is actual and restores ws.

Deleting b removes every s-to-z path, since b originally covered; the
new st still has no t-to-z suffix. Every original bypass of r used p,
by the r-cover hypothesis in S-p. Hence r now covers. The edge p covers
by (1), and the last flip is actual. Its result is T.

### A four-flip row

**Proposition.** Suppose ws,b,c are selected covers in S, wt covers
in S, and r covers in S-p. Then S and T are connected by

    xs -> wx [retain ws],
    wx -> xt [retain wt],
    tz -> st [retain sz],
    xt -> tz [retain r].                             (4)

The first flip is actual: p and ws cover, and after deleting p there is
no x-to-s path. The new wx is adjacent. Since there is no x-to-t path
after deleting p, it does not bypass wt. The second flip is therefore
actual and selects xt as a cover. Neither of these changes affects a
path starting at s or t, so the third flip is actual by the original
covers of b,c and the absence of an s-to-t path.

At this point r covers. Original bypasses used p, now absent. A bypass
using the new st would require an x-to-s path, which is absent; a bypass
using xt would require a t-to-z path after deleting c, also absent because
c covered. The edge xt covers for the same x-to-s reason, so the last
flip is actual and restores c. The final relation is T. No cover of f
is required at any stage.

### A five-flip row

**Proposition.** Suppose ws is absent, b,c,wt are selected covers in S,
f covers in S-c, and r covers in S-p. Then S and T are connected by

    tz -> st [retain sz],
    sz -> ws [retain f],
    xs -> sz [retain r],
    st -> tz [retain sz],
    ws -> st [retain wt].                            (5)

The first flip is actual by (1) and the covers of b,c. It exposes f,
since c was its only possible source of bypasses and the new st has no
t-to-z suffix. In S-c the cover of f and the selected b also exclude
a w-to-s path. Hence the second flip is actual. Removing b removes every
s-to-z path except one that could continue through st; its t-to-z suffix
is still absent. The r-cover condition in S-p now exposes r, making the
third flip actual.

The fourth flip reverses the first triangle. The newly restored b and
the selected st cover; there is no t-to-z path before this reversal.
At the last step, wt still covers: the new ws cannot bypass it without
an s-to-t path after st is removed. That path was absent in Q, and the
other changes cannot create it. The edge ws also covers, since it was
introduced when no w-to-s path existed and subsequent changes do not
create such a path. Thus the last flip is actual and leaves T.

All shorts in (2)--(5) and the branch rows are normal, since they lie
properly inside f. The argument restores every exterior edge and does not
invoke a component expansion or any restriction on cycle rank.

## Recovery verification and the remaining obstruction

Primary self-checked the new arguments and tested the displayed rows with
the existing exact Rust cover/flip functions. No new independent reviewer
was launched after the crash. The old consultation output was empty.

Related Rust: the existing external `first_join_tree_lifts.rs` now accepts
`--retained-exterior --recovery-check`. It checks each displayed move,
strict-edge preservation, and the exact final relation for every applicable
selection in the same two fixtures as before. Overlapping hypotheses are
counted separately. In area011234 the three new redundant-anchor rows
cover the three previously uncovered pairs. In area0112345 they apply to
39,42,39 pairs respectively. The right-hand preparation applies four times,
and the branch construction twice; together they cover the three remaining
r-cover pairs in that fixture. Of the 310 pairs with neither anchor covering,
190 remain outside all the proved sufficient conditions. These counts are
finite coverage evidence, not a proof that these cases exhaust a general
exterior.

The unrestricted r-cover case and unrestricted neither-cover case are still
open. In particular, a longer w-to-s branch need not satisfy the branch
proposition, and additional bypasses can prevent the conditional covers in
(3)--(5). The left retained-e-prime repair and whole-component reassembly
also remain open. The current receipts and source snapshot are under external
`dn-crash-recovery-20260929/`. No Lean/Lake build or manuscript proof change
is involved.
## Continuation: moving along a selected suffix

2026-09-29. The preceding recovered text is unchanged. The following
construction handles a family in which both original anchors are redundant;
its length depends on a saturated exterior path, rather than on the number
of vertices in the displayed recurrence.

**Proposition.** Keep S=Q+xs and T=Q+st and all hypotheses of the original
configuration. Suppose ws and wt are selected covers in S, xz covers in Q,
and Q has no path from t to z. Suppose there is a selected cover sv, with
t<v<=z, and a selected path from v to z. Then S and T lie in the same
complete source component, with every other selected edge restored.

We choose a saturated path

    v=v_0<v_1<...<v_m=z.

It may be trivial when v=z. We first perform

    xs -> wx [retain ws],
    wx -> xt [retain wt].                            (6)

The first move is actual because ws and xs cover. It does not destroy
the cover of wt: a new bypass would use wx followed by an x-to-t path
in Q, excluded by (1). The second move is therefore actual. After (6)
the relation is Q+xt. The edge r=xz covers there: it covers in Q, and
a new bypass through xt would require the forbidden t-to-z suffix.

Borrow xv backwards along the chosen path. For i=m-1,...,0 perform

    v_i v_(i+1) -> xv_i [retain xv_(i+1)].           (7)

The current long edge covers. The path short covers because the path
was saturated and preceding changes only deleted path edges and added
edges starting at x<v. An existing x-to-v_i path would bypass the
current long. Thus every flip is actual, and its new short supplies
the next covering long. The edge xt still covers, since the new edges
from x all end at or beyond v>t. Now perform

    xt -> tv [retain xv].                           (8)

This is actual by the two cover tests just obtained. We undo (7) in
reverse order. The only extra edge relative to the corresponding forward
states is tv, in place of xt. There is no remaining x-to-t path: it was
absent in Q, and every added x-edge ends above t. Thus tv cannot bypass
any tested long or short beginning at x. The other tested edges start
at or beyond v, so tv cannot bypass them either. All reverse flips are
actual, leaving exactly Q+tv.

Finally sv is still a cover: a new bypass through tv would require the
absent s-to-t path in Q. The edge tv is a cover too; all restored path
edges start at or beyond v and cannot affect its cover test. We may use

    tv -> st [retain sv].                           (9)

The resulting relation is exactly T. There are 2m+4 actual flips. Every
exchanged edge is a proper subinterval of the natural corner f=wz, so
it is normal. All other strict edges and the complete exterior remain
unchanged at the end.

Both f and r are redundant in S: they have the respective selected
bypasses w->s->v->...->z and x->s->v->...->z. Thus this proposition
does not assume that an original outer anchor covers. It does assume
the displayed branch covers and the cover of r after deleting xs.

For the previously uncovered seven-vertex state

    S={01,13,14,16,23,26,35,56},

take (w,x,s,t,v,z)=(1,2,3,4,5,6). The six flips are

    23->12 [13], 12->24 [14], 56->25 [26],
    24->45 [25], 25->56 [26], 45->34 [35].

They restore the entire suffix and replace only 23 by 34. This is now
an instance of the arbitrary-length proof, not just the recorded BFS path.

## Using a shorter pair of anchors

The earlier covering-f proposition also works with an auxiliary endpoint
v satisfying t<v<=z, provided wv and xv are selected and wv covers in S.
We retain the original natural corner wz to ensure that all exchanged
edges are normal, and run that proposition's incoming sweep, outgoing
sweep and three-flip repair with v in place of z. All their tested
intervals lie in [w,v]. Edges with an endpoint above v cannot occur
in a forward path testing one of those intervals. Neither the proof
nor its restoration requires wv itself to be strict.

For example, the recorded states

    {01,14,15,16,23,25,26,56},
    {01,13,14,15,16,23,25,26,56}

use v=5, with original z=6. The covering anchors 15,25 give the two
three-flip rows already recorded in the exact receipt. The redundant
original edges 16,26 and the selected suffix 56 remain fixed.

## Verification of this continuation

Related Rust: the existing external `first_join_tree_lifts.rs` consumer,
new option `--branch-suffix-check`, reuses `component_source_probe::cover`
and `component_source_probe::flip`; no cover or flip model is reimplemented.
It checks every instance of the proposition in the same fixed natural
diagrams as the recovery run: one pair at area 011234 and 46 pairs at
area 0112345, respectively 4 and 192 actual flips, with exact exterior
restoration. One explicit eleven-vertex state checks a five-edge suffix
and all 14 flips; no eleven-vertex state space is enumerated.

Receipts and preserved before-files are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/dn-notebook-continuation-20260929/`.
The library guide, Cargo package metadata and existing Rust APIs were
checked before extending the consumer. Maintained Rust sources are unchanged.
These checks support the proof above, not a claim of unrestricted coverage.
The earlier 190 uncovered-pair count predates these two observations; we
have not recomputed an updated coverage partition. The unrestricted
retained-edge statement, the left retained-e' repair and simultaneous
whole-component collection remain open.

## Clearing the obstructing part of an incoming cut

2026-09-29 continuation. We retain the notation of the opening configuration
and all exterior edges. This gives another arbitrary-exterior reduction to
the proved two-cover lemma. It allows multiple incoming branches and does
not assume any cycle-rank bound.

Suppose r covers in S=Q+p and t does not reach z in Q. Define

    I={v : x<v<z, vz is selected in Q, w reaches v in Q},
    B={v in I : v reaches s or t in Q}.

**Proposition.** If wv is absent for every v in B, then

    Q+p ~ Q+j.                                       (C1)

The hypothesis concerns the direct edges wv, not the existence of paths:
by definition w already reaches each such v. The anchors may initially
have different cover status; only r is required to cover.

First process I in decreasing order, replacing vz by xv while retaining r.
Every vz covers when processed: a bypass ends at a later uz that was already
removed. The cover of r excludes an existing x-to-v path, and the added
edges start at x, which w cannot reach because x=w+1 and wx is absent.
Thus this is an actual incoming sweep, it preserves r as a cover, and it
clears every bypass of f. Both anchors now cover.

Only the new xv with v in B can introduce unwanted x-to-s or x-to-t paths.
We transfer these edges to w one at a time, in increasing order of v, using
the covering-arm lemma in
[the two-anchor transfer](COMPONENT_RIGHT_ARM_TRANSFER.md#arbitrary-exterior-transfer-with-two-covering-anchors).
The anchors are xz,wz, the transferred arm is xv, and wv is absent by
hypothesis.

To justify the cover test for xv, an original x-to-v path is excluded by
the original cover of r together with the selected vz. Any new bypass
must start with an earlier new xy and then reach v. Such a y also reaches
s or t, hence lies in B; its edge xy was already transferred to wy. Later
new edges cannot reach v. The original p=xs cannot start this bypass either:
if v reaches s this contradicts the vertex order, and if v reaches t it
would give the forbidden s-to-t path. Thus xv covers at every transfer.
Each transfer restores its temporary edges and leaves both anchors covering.

Let S*=Q*+p be the resulting state. Relative to the original S, its only
changes are

    vz -> wv for v in B,
    vz -> xv for v in I\B.

There is no x-to-s or x-to-t path in Q*: original such paths were excluded,
and every remaining new xv has v outside B. New edges starting at w are
unreachable from x. There is still no s-to-t path. The edges f,r,wt remain
selected, and f,r cover in S*. Therefore the opening two-cover lemma,
with y=w, gives S* ~ Q*+j.

We finally undo the full preparation. We must check this in the presence
of j, not infer it merely from the path on S. Every preparation edge starts
below t or is an incoming edge to z. The auxiliary incoming edges used
inside a transfer have tails below its arm endpoint v<t. Consequently
the preparation never creates a t-to-z path. Adding st cannot bypass any
tested edge ending at z.

For the initial incoming sweep, the other tested edges are xv with original
vz selected. A bypass using st would require t to reach v. Below z this
reachability is unchanged by the preparation, since all new edges start
at w or x, and within a transfer all additional heads below z are below t.
An original t-to-v path, followed by vz, would contradict t not reaching z.
For each subsequent arm-transfer sweep, all tested edges not ending at z
have heads at most its endpoint v<t, so st cannot bypass them either.
Deleting p cannot spoil any cover. The very same preparation is therefore
actual on Q+j, and its inverse restores every exterior edge after the
two-cover repair. This proves (C1).

The condition may fail when wv is already selected at an obstructing
incoming branch. We have not proved a transfer that absorbs that common
branch without changing the other edges. The proposition does not settle
all r-cover cases, the cases with both anchors redundant, or left
retained-e-prime reassembly.

### Exact checks with more than one incoming branch

Related Rust: external `first_join_tree_lifts.rs`, function
`retained_cut_preparation`, option `--retained-cut-check`. The diagnostic
checks the preparation at BOTH endpoints Q+p and Q+j, every actual flip,
strict-edge preservation, the exact prepared endpoints and all hypotheses
of the already-proved two-cover lemma. The middle lemma is used as proved
above; this diagnostic does not construct its middle path anew.

Two explicit states, with only 01 and 1z strict, are checked:

| n | (w,x,s,t,z) | Selected edges | Obstructing vertices B | Preparation plus inverse |
| --- | --- | --- | --- | ---: |
| 8 | (1,2,5,6,7) | 01,17,27,16,25,13,34,47,45 | {4} | 10 flips |
| 10 | (1,2,7,8,9) | 01,19,29,18,27,13,34,45,49,59,47,57 | {4,5} | 24 flips |

No state space on eight or ten vertices is enumerated. The hypotheses
and proofs retain arbitrary exterior; these are exact checks of the new
preparation, not a claim of exhaustive retained-edge coverage.
Receipts and preserved before-files are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/two-anchor-transfer-20260929/`.

## Sliding the moving edge along crossing covers

2026-09-29 continuation. We give a direct local-diagram construction which
does not require either f or r to cover. It retains the same background Q
at every step and moves only the additional edge incident with s.
The criterion is sufficient for the unrestricted retained-edge problem;
we do not assert that every Q satisfies it.

**Crossing-cover lemma.** Let Q be a selected forward relation in an
ordinary interval-closed natural diagram, containing all its strict edges.
Fix a vertex s. Take vertices

    v_0=x, v_1, ..., v_m=t,

alternately below and above s, where x<s<t. Suppose that for every i:

- if v_i<s, Q has no v_i-to-s path;
- if v_i>s, Q has no s-to-v_i path;
- for each consecutive pair, the edge joining its smaller to its larger
  endpoint is selected and covers in Q.

Then Q+xs and Q+st are connected by m actual flips. Every edge of Q is
retained throughout. There is no adjacency, cycle-rank or anchor hypothesis.
All reachability and cover conditions refer to the full Q, with its exterior.

**Proof.** Write h(v)=vs for v<s and h(v)=sv for v>s. Each h(v_i)
is absent from Q by its corresponding reachability condition. For one
consecutive pair a<s<b, its selected long edge ab covers in Q, while
Q has neither an a-to-s path nor an s-to-b path. In Q+as, the new as
covers. The only new possible bypass of ab would use as followed by an
s-to-b path, which is absent. Thus as->sb [retain ab] is actual.
Equivalently, in Q+sb a new bypass of ab would need an a-to-s path;
the reverse flip is actual as well. This proves each step

    Q+h(v_i) <-> Q+h(v_(i+1)).

Their concatenation proves the lemma. Each exchanged edge is a proper
short of a selected natural long edge, so it is natural and cannot be a
strict corner. All other edges, including those incident with s already
in Q, remain untouched. This proves the arbitrary-exterior statement.

The criterion is also necessary for a path constrained to retain every
edge of this same Q and move only one additional edge incident with s.
Each step must retain an edge ab of Q with a<s<b. Its long-edge cover
implies that ab covers in Q. The two endpoint short covers imply that Q
has no a-to-s or s-to-b path. Hence each step uses exactly an edge allowed
by the criterion. Failure to find such a path means that a proof must
temporarily change some background edges; it does not imply that the two
states belong to different components.

### A direct repair with both original anchors redundant

For example, on six vertices put (w,x,s,t,z)=(0,1,2,4,5) and

    Q={03,04,05,13,15,35,45}.

The original anchors 05,15 are both redundant. Nevertheless 13,03,04
are covers in Q and give the alternating path 1,3,0,4 across s=2.
The lemma gives

    12 -> 23 [retain 13],
    23 -> 02 [retain 03],
    02 -> 24 [retain 04].

This moves xs to st directly. It does not transfer wt to xt. Indeed,
the latter intermediate transfer is false in general, even when x does
not reach t, as proved in the
[outgoing-arm obstruction](COMPONENT_RIGHT_ARM_TRANSFER.md#why-absence-of-a-target-path-does-not-replace-the-anchor-covers).
One may add a new vertex before w with its strict edge to w, shifting all
labels by one, to place this example in an actual saturated DN source.
That edge cannot affect any displayed cover test.

The path need not have three steps. For a fixed ten-vertex example, let
s=5, x=1, t=8, with the original anchors 09,19 and arm 08, and set

    Q={09,19,08,16,26,27,37,38,69,79,89,05,45,59}.

The crossing covers 16,26,27,37,38 give the path

    1,6,2,7,3,8.

Thus 15 becomes 58 in five actual flips, retaining all of Q. Both
original anchors are redundant, and Q has both incoming and outgoing
edges at s. The latter shows why the proof uses precise reachability
conditions instead of assuming that s is isolated in the background.

The same lemma applies to a left retained-e-prime comparison ut versus tx,
using t as the moving-edge vertex and Q equal to the source with ut removed.
When its crossing-cover path exists, it proves the required h01 equality;
the opposite-defect identity then supplies the corresponding t00 equality.
Existence of such a path is an additional hypothesis, not a consequence of
the first-drop geometry proved so far.

### Verification and scope

Related Rust: the existing external `first_join_tree_lifts.rs`, option
`--crossing-cover-check`, constructs the permitted crossing-edge paths and
checks each actual flip with `component_source_probe::flip`. Among the
576 retained-edge comparisons in one fixed complete six-vertex diagram,
56 satisfy this criterion, including 10 with both original anchors
redundant. Their 168 flips pass, with exact endpoints and strict edges
preserved. The fixed ten-vertex example passes all five flips and checks
the full exterior; no ten-vertex state space is enumerated.

These checks do not cover the other 520 comparisons by this construction.
Other proved repairs may apply to them; no new exhaustive coverage partition
is claimed. The unrestricted retained-edge proof, unrestricted left repair
and simultaneous whole-component collection remain open. No new independent
review is claimed. No Lean/Lake build, worker, consultant, manuscript build
or maintained Rust change was used.
Receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/outgoing-no-path-20260929/`.

## An incoming covering anchor with a path to t

2026-09-29 continuation. Keep the opening configuration S=Q+xs and
T=Q+st, with w<x<s<t<z, x=w+1 and the three absent paths in (1).
We extend the earlier path construction to an anchor whose tail may lie
BEFORE s. Stopping the path preparation one edge before t is essential.

**Proposition.** Suppose r=xz covers in S. If there is a selected
covering yz with x<y<t and a selected path from y to t in Q, then
S~T, with every other edge restored. We do not require f to cover,
a direct edge yt, or a bound on exterior size or cycle rank.

The cover of yz and the y-to-t path imply that t does not reach z.
Choose a path of selected covers

    y=v_0 < v_1 < ... < v_m=t.

Such a path exists by refining any selected path. It lies in Q since
its tails exceed x. Put h=v_(m-1). We have h!=s, because s does not
reach t. For i=0,...,m-2, exchange

    v_i v_(i+1) -> v_(i+1)z [retain v_i z].         (24)

Every step is actual. The current long covers, and earlier changes
cannot spoil a path-edge cover: their new edges end at z above t, while
all other changes are deletions. Each newly introduced v_(i+1)z covers
and supplies the next long. We stop with hz covering and ht still selected.
The latter remains a cover as well.

The preparation preserves r. In the original S, x cannot reach any path
vertex: a path avoiding xs would contradict Q's absence of x-to-t, and
a path using xs would contradict the absence of s-to-t. New edges ending
at z do not change this reachability below z. The same observation preserves
all three conditions in (1). No step removes f,r,wt or xs.

If h<s, apply the opening two-covering-edge lemma with y=h. The edges
hz,ht supply its auxiliary triangle; it replaces xs by st and restores
the complete prepared background. Its outgoing cut handles all competing
h-to-s paths, including a redundant selected hs.

If h>s, use the already-proved five-flip row

    ht -> tz [hz],       tz -> xt [r],
    xs -> st [xt],       xt -> tz [r],
    tz -> ht [hz].                                  (25)

This is the one-edge case of the earlier right-of-s path construction.
It too restores the prepared background while changing only xs to st.

Finally undo (24). No t-to-z path has been created: all newly added
edges ending at z have tails at most h<t. A new bypass of any retained
v_i z using st would need the absent t-to-z suffix. The other tested
intervals end at or before h<t, so they cannot use st at all. Removing
xs only destroys bypasses. Hence every inverse is actual and the entire
original exterior is restored. This proves the proposition.

For h<s, if the opening lemma uses c outgoing-cut edges, the construction
has 2(m-1)+2c+3 flips. For h>s it has 2(m-1)+5 flips. The older assumption
y>s is sufficient but no longer necessary. Simply pushing the final ht
all the way to tz when h<s would lose the inverse argument; the two-cover
repair at h supplies the missing order of operations.

### The last obstructing incoming branch reaches t

This gives a further case of the earlier incoming-cut reduction, including
selected direct common arms. Suppose r covers and t does not reach z,
and use the original sets

    I={v : x<v<z, vz selected in Q, w reaches v in Q},
    B={v in I : v reaches s or t in Q}.

**Proposition.** If B is nonempty and its largest member v reaches t,
then S~T. No assumption is imposed on any selected direct wv arm.

Process just the members h of I with h>v, in decreasing order, replacing
hz by xh while retaining r. These are actual incoming-cut flips by the
same last-edge argument as before. They expose vz: every bypass of vz
would end in kz with k>v reachable from v, hence reachable from w and
already processed. The edge r remains covering.

By the maximality of v in B, none of these larger h reaches s or t.
Their new xh edges therefore preserve the three conditions in (1).
Reachability from v to t is unchanged, since all removed edges end at
z and all new edges start below v. We have obtained the hypotheses of
the preceding proposition with y=v. Apply it to replace xs by st.

Undo the truncated incoming cut. The new st cannot bypass a tested edge
ending at z, since t still does not reach z. It cannot bypass a tested
xh either: after xs is removed, x does not reach s, and neither the
preparation nor its inverse creates such a path. All shorts are still
selected as required, so each inverse flip is actual. This restores Q.

This treats cases excluded by (C1) because wv is already selected,
including a redundant vz before the truncated cut. Combining the two
propositions with the earlier cases sharpens the remaining r-cover
obstruction: outside the proved repairs, the largest member of B must
reach s and NOT t, and (C1)'s absent-direct-arm condition must fail.
We have not repaired that remaining common branch in full generality.

### Where a retained-edge coefficient defect can occur

There is also a useful support consequence of the older covering-f
proposition. If f covers at EITHER endpoint S or T, then S~T.
To see the reverse direction, note that w cannot reach x, since they
are adjacent and wx is absent. Adding xs therefore cannot create a
bypass of f. If f covers in T, removing st preserves its cover and
then adding xs still preserves it, so f covers in S as well.

For any source-component function h, a nonzero difference h(S)-h(T)
therefore forces f redundant at both endpoints. The one-corner alternating
valuations partial_f X(S)=X(S)-X(S-f) and partial_f X(T) vanish, for X=K,E.
In particular, this retained-edge defect cannot touch a mixed-acyclic
source state when f is strict. This parallels the three-corner support
restriction for the genuine-DN left comparison, but does not resolve a
path through zero states or the other mixed-sector coefficient equations.
It is not an assertion that the two whole source components are reducible.

### Fixed checks

Related Rust: external `first_join_tree_lifts.rs`, option
`--retained-reachable-anchor`, using the existing exact cover/flip oracle.
Three fixed ten-vertex states exercise a path of length three with its
last predecessor on either side of s. The two left-side cases include an
outgoing cut and respectively absent and redundant selected hs. All three
paths use nine flips and restore every exterior edge.

One fixed eleven-vertex state has I={3,9}, B={3}, s=7,t=8,z=10.
Its direct common arm 13 is selected and anchor 3,10 initially redundant.
The truncated cut removes 9,10, exposing the reachable anchor at 3;
the full eleven-flip path restores every other edge. Every actual flip,
strict edge and endpoint is checked. No state space is enumerated.
Sources, exact edge lists and receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/retained-reachable-anchor-20260929/`.
The full previous note remains a verbatim prefix. No Lean/Lake build,
new worker, consultant, maintained Rust edit or independent review was used.

## A shared branch reached by an arbitrary prefix

2026-09-29 continuation. We treat part of the remaining branch reaching s
but not t. The direct shared arm wy may be absent or redundant. We use
an arbitrary selected w-to-y path and restore it after removing the edge
through which every w-to-s path passes.

Keep S=Q+xs, T=Q+st and the opening conditions. Suppose

    w<x<y<s<t<z,
    r=xz, wt, yz, ys cover in S,
    w reaches y,       t does not reach z,
    w does not reach s in S-ys.                      (26)

The last condition says that every w-to-s path uses ys. In particular
ws is absent. Given selected ys and w reaching y, it also implies that
ys covers; we have displayed that cover to make the local tests explicit.

**Proposition.** Under (26), S~T, with every other selected edge restored.
There is no uniqueness assumption on the w-to-y path and no cycle-rank
bound. A selected direct wy need not cover. If the chosen saturated prefix
has m edges, the construction uses 2m+3 flips.

Choose a path of selected covers

    w=v_0 < v_1 < ... < v_m=y.

It cannot use x because w,x are adjacent and wx is absent. All its
vertices after w therefore lie strictly between x and s. For
i=0,...,m-1, exchange

    v_i v_(i+1) -> v_(i+1)t [retain v_i t].          (27)

The first long is the covering wt. At each later step the preceding
actual flip supplies the new covering long. Its selected path short
still covers: all earlier added edges end at t>y, and deletions cannot
create a bypass of a path short. Thus every step is actual. The final
edge yt covers, and ys still covers. We do NOT require the earlier
longs v_i t to remain covering after later steps; competing prefix paths
can make them redundant temporarily.

The edges r and yz remain covering. Their only possible new bypasses
would use one of the inserted v_i t and then a t-to-z suffix, which
does not exist. No preparation creates such a suffix: all its added
tails lie below t. The short xs remains covering, because all new heads
are above s. Conditions (1), tested after omitting xs, are preserved.
In particular, x cannot acquire a path to t through a new v_i t,
since an old x-to-v_i path would imply an old Q-path to s. The selected
xs cannot reach v_i<s either.

Now exchange

    ys -> st [retain yt].                            (28)

This is actual by the two displayed covers. Before undoing (27), note
that none of its path vertices v_i can reach s without ys. Otherwise
the original w-to-v_i prefix followed by that path would give a w-to-s
path avoiding ys, contradicting (26). The new edges ending at t>s
cannot create a path to s, and restoring old prefix edges cannot create
a path absent in the original S-ys.

Consequently we may undo the whole prefix (27). Relative to the recorded
inverse, ys has been removed and st added. Removal only helps covers.
The new st could bypass a tested edge v_i t only through a v_i-to-s path,
which we have just excluded. All other tested intervals end at or before
y<s, so they cannot use st. Every reverse flip is actual. This restores
the full prefix and removes all artificial v_i t except the original wt.

We have reached Q-ys+xs+st. Finish with

    xs -> sz [retain r],
    sz -> ys [retain yz].                            (29)

The edge r still covers, because st has no t-to-z suffix; xs still
covers because no new edge ends at or below s. The first flip therefore
creates a covering sz. The original cover of ys implies that y does
not reach s after ys is removed. Thus the new sz does not bypass yz,
and the second flip is actual. It restores ys and leaves exactly Q+st.
This proves the proposition. The edge wt may become redundant at the
final endpoint; it is not retained after that happens.

All exchanges are normal: (27)--(28) lie properly inside wt, and (29)
inside the selected natural edges r,yz. The complete exterior participates
in every cover test. This is an actual-component argument, not a claim
that either valuation is constant on an individual flip.

### Application after a truncated incoming cut

Return to the sets I,B of the preceding section. Suppose r and wt cover,
t does not reach z, and the largest member y of B reaches s but not t.
Suppose ys is selected and w does not reach s after removing ys.
Then S~T even if yz starts redundant or wy is selected and redundant.

Indeed, the same truncated cut at h>y exposes yz while preserving r
and (1). Its added xh are unreachable from w; below z the w-to-y and
w-to-s relations are unchanged. The new heads h do not reach s or t,
so the cover of wt is preserved. The cover of ys also persists, and
the condition after deleting ys is unchanged. Apply (26)--(29), then
undo the truncated cut exactly as in the preceding proposition.

This closes the stated common-branch case, not every branch reaching s.
There may be several w-to-s routes with no shared selected final edge,
the common final edge may have no suitable covering yz after preparation,
or wt may be redundant. Those configurations still need a general repair
or a coefficient correction. Whole-component reassembly remains open.

### Fixed path checks

Related Rust: external `first_join_tree_lifts.rs`, option
`--retained-shared-prefix`. Two fixed n10 states have a three-edge
w-to-y prefix and a selected redundant wy. One also has competing
prefix paths; two earlier artificial anchors become redundant before
the central exchange. Both nine-flip paths pass every actual cover test
and restore the exact exterior.

A fixed n11 state adds the truncated incoming cut: y=5,s=7,t=8,z=10,
I={5,9}, B={5}; the anchor 5,10 is initially redundant and the direct
shared arm 15 is redundant. Its eleven-flip path also passes. No state
space is enumerated. Exact edge lists, sources and receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/retained-shared-prefix-20260929/`.
Every previous retained-edge paragraph is preserved as a verbatim prefix.
No Lean/Lake build, worker, consultant, maintained Rust edit or new
independent review was used.

## Several routes entering s

2026-09-29 continuation. We remove the common-final-edge condition in
(26). We restore the prefix while st is temporarily replaced by tz.
Both temporary edges then end above every interval tested by the inverse
prefix. Competing routes into s cause no difficulty, even when they enter
from before y. The selected ys may also start redundant.

Keep the opening configuration S=Q+xs, T=Q+st. Suppose

    w<x<y<s<t<z,
    r=xz, wt, yz cover in S,
    ys is selected,       w reaches y,
    t does not reach z.                              (30)

**Proposition.** Under (30), S~T with every other selected edge restored.
The exterior and cycle rank are arbitrary. We require neither a least
incoming tail nor a common edge on the w-to-s paths.

### Expose ys and prepare the prefix

First process increasingly every selected yv with y<v<s and v reaching
s in S. Exchange yv->vz while retaining yz. Each yv covers at its turn:
a bypass would start with an earlier qualifying outgoing edge, already
removed. Added edges end at z and cannot create such a bypass. Each
exchange preserves the cover of yz, and the cut exposes the selected ys.
Denote this preparation by O, with o flips, and its resulting state by S0.

The cut also preserves r. An old x-to-v path would imply an old Q-path
from x to s, and xs cannot reach v<s. Thus no new vz bypasses r.
New heads z lie above t, so wt remains covering. The cut changes nothing
at or below y, and no new edge starts at or above t; w still reaches y
and t still does not reach z. Conditions (1), after omitting xs, persist.

Choose a saturated selected prefix

    w=v_0 < v_1 < ... < v_m=y.

It cannot use x because w,x are adjacent and wx is absent. For
i=0,...,m-1 exchange

    v_i v_(i+1) -> v_(i+1)t [retain v_i t].          (31)

Call these m flips P. The first retained long wt covers; each actual
flip supplies the next covering long. Earlier added edges end above y,
so every original prefix short still covers when used. The final yt
covers. Earlier longs may become redundant through competing routes;
we do not retain them again until their recorded inverse step.

Both r and yz remain covering because no t-to-z suffix exists. The
edge ys remains covering because new heads t exceed s. The edge xs
also remains covering. No prefix move creates a t-to-z suffix.

### Temporarily remove st before restoring the prefix

Use the three flips

    xs -> sz [retain r],
    ys -> st [retain yt],
    st -> tz [retain sz].                            (32)

The first two use the covers just proved. In the second, the newly added
sz ends above t and cannot interfere. Before the third, sz still covers:
adding st could bypass it only if t reached z. Thus the third flip is
actual. It leaves sz and tz selected, with xs,ys,st absent.

Now undo all of P in reverse order. Relative to its recorded states,
xs and ys have been deleted and sz,tz added. Every tested interval is
contained in [w,t]. The added edges both end at z>t and cannot occur on
any tested forward path. Deletion cannot create a bypass. Neither xs
nor ys is a tested edge: x is not a prefix vertex and s>y. Every inverse
is therefore actual. The full original prefix is restored, even when
an earlier long would have been redundant had st remained selected.

The resulting state is S0-xs-ys+sz+tz. Finish with

    tz -> st [retain sz],
    sz -> ys [retain yz].                            (33)

For the first flip, sz and tz cover. In S0 we have s not reaching t by
(1), and s not reaching z because r covers with xs selected. The cut O
has preserved these facts. Therefore the two displayed new edges are
the only possible new paths from s or t to z; neither bypasses the other.

After tz->st, t again does not reach z. Since ys covered in S0, removing
it leaves no y-to-s path. The new st cannot alter that fact. Consequently
sz cannot bypass yz, and st cannot bypass yz without a t-to-z suffix.
Thus yz and sz cover, making the last flip actual. We reach S0-xs+st.

Finally undo O. Relative to each original cut state, xs is removed and
st added. A new bypass of yz or vz would require a t-to-z suffix, still
absent; a tested yv ends below s and cannot use st. Every inverse is
actual. We have restored every original edge except xs and inserted st.
This proves the proposition with 2(o+m)+5 flips.

All exchanges are normal: (31) lies properly inside wt, and the remaining
exchanges lie properly inside yz, r, yt or sz, themselves natural edges.
The complete exterior participates in every cover test. We have proved
an actual component path, without assuming invariance of either valuation
under an individual flip.

### The last obstructing incoming branch

Use the earlier sets I,B. Suppose r and wt cover, t does not reach z,
and the largest y in B reaches s but not t. If ys is selected, then
S~T even when yz and ys are initially redundant.

Apply the truncated incoming cut at heads h>y to expose yz. It preserves
r,wt, the selected ys, and all w-reachability below z: its added xh are
unreachable from w, and these heads do not reach s or t. Conditions (1)
and t not reaching z persist. Apply (30)--(33), then undo the truncated
cut by the earlier inverse argument. If the cut has a flips, the full
path has 2(a+o+m)+5 flips.

This treats arbitrary competing routes into s when the displayed ys is
selected. Neither an earlier incoming tail nor redundancy of ys is an
obstruction. The remaining s-reaching cases outside this construction
include missing ys and redundant wt. Cases with both original outer
anchors redundant, the unrestricted left comparison, and general
whole-component reassembly still require further arguments.

### Fixed checks

Related Rust: external `first_join_tree_lifts.rs`, option
`--retained-temporary-suffix`. Four fixed n10/n11 states use
w=1,x=2,y=4,s=7,t=8, with incoming edges 37,47,57,67. Thus an incoming
tail precedes y, and ys is not common to all w-to-s paths. All have
competing prefix routes and redundant direct wy. Two also select 45,46,
making ys redundant; the n11 states first expose the redundant yz.

The four paths have 9,13,11,15 flips. Each explicitly checks that the
earlier temporary long 38 is redundant after ys->st, so simply reversing
the prefix at that point would fail. Temporarily replacing st by tz
makes the full inverse valid. Every actual flip, strict edge and exact
endpoint passes the existing oracle. No state space is enumerated.
Sources, full edge lists and receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/retained-incoming-s-20260929/`.
The complete prior retained-edge note remains a verbatim prefix. No
Lean/Lake build, worker, consultant, maintained Rust edit or independent
review was used.

## A path to s in place of a selected ys

2026-09-29 continuation. We remove the selected-ys hypothesis in (30).
In its place we assume only that y reaches s. We supply the temporary
sz from a selected suffix path after the central exchange.

**Proposition.** Keep the opening Q conditions and suppose

    w<x<y<s<t<z,
    r=xz, wt, yz cover in S=Q+xs,
    w reaches y,       y reaches s,
    t does not reach z.                              (34)

Then S~Q+st with every other edge restored, with arbitrary exterior and
cycle rank. The edge ys need not be selected. If it is selected, the
preceding proposition applies, including when it is redundant.

Suppose therefore that ys is absent. Perform the outgoing cut O of the
preceding proof: process increasingly all selected yv with y<v<s and
v reaching s, exchanging yv->vz while retaining yz. The same cover
arguments apply. This time the resulting state S0 has no y-to-s path.
The cut is nonempty, since y originally reaches s. Let v be its largest
processed head. The last flip makes vz a cover, and v still reaches s:
all deleted edges start at y<v, and all added edges end at z>s.
The edges r,wt,yz cover, and w still reaches y.

Use the saturated w-to-y prefix P from (31) to obtain a covering yt.
It does not affect the cover of vz or a path from v to s: its added
edges end at t>s with tails at or below y<v; its deleted edges have
heads at or below y. Now use

    xs -> sz [retain r],
    sz -> ys [retain yz],
    ys -> st [retain yt].                            (35)

The first flip is actual by the preserved covers. For the second, y
does not reach s in S0 or after P, so the new sz cannot bypass yz.
The resulting ys covers. Adding ys cannot bypass yt because s does not
reach t; the prefix preparation only adds edges with tails at or below
y<s and hence has not changed that fact. The third flip is actual.
We have replaced xs by st, but may not yet be able to undo P.

### Borrow sz from the remaining suffix

Choose a saturated selected path

    v=a_0 < a_1 < ... < a_k=s.

It still exists after (35), and its edges still cover: changes outside
O that could affect it have heads above s or tails below v. Starting
with the covering vz, perform

    a_i a_(i+1) -> a_(i+1)z [retain a_i z],
    i=0,...,k-1.                                    (36)

Denote this preparation by H. Each new short supplies the next covering
long. Earlier added edges end at z>s, so cannot spoil a path short.
The initially covering vz remains covering through (35): st could
bypass it only through a t-to-z suffix, which does not exist. Thus H
is actual, and its last step supplies a covering sz. The short st
still covers because H adds only edges ending above t. Exchange

    st -> tz [retain sz].                            (37)

We can now undo P. Relative to its recorded states, xs is removed,
tz and the incoming-to-z edges of H are added, and the path shorts of
H are deleted. No added edge can affect an interval in [w,t]. None
of the deleted H shorts is tested by P: their tails are at least v>y
and their heads at most s<t, whereas P tests prefix edges with heads
at most y and long edges ending at t. Every inverse of P is actual.

Next reverse (37), exchanging tz->st while retaining sz. Restoring P
cannot affect its cover tests: all changed tails are at or below y<s,
while the tested intervals lie in [s,z]. Hence this inverse is actual.
Now undo H. Every interval tested by H starts at or above v>y, so the
restored prefix cannot affect any test. Relative to the recorded H
states, that is the only remaining difference. Thus the full inverse
of H is actual and restores the entire v-to-s path.

Finally undo O. The state differs from its recorded endpoint only by
xs removed and st added. As before, st cannot bypass any edge ending
at z without a t-to-z suffix; the other tests end below s. Each inverse
is actual. We finish at exactly Q+st, with ys absent as it was initially.
If O,P,H have o,m,k flips, the path has 2(o+m+k)+5 flips. All exchanged
edges are proper shorts of selected natural longs, hence normal.
This proves the proposition.

### All comparisons with r and wt covering

**Corollary.** Under the opening Q conditions, if r and wt cover in
Q+xs, then Q+xs~Q+st, with no further exterior hypothesis.

If t reaches z, use the earlier selected-suffix repair. Otherwise form
I,B as above. If B is empty, (C1) applies vacuously. If B is nonempty,
let y be its largest member. When y reaches t, use the earlier
truncated-cut/reachable-anchor proposition. In the remaining case y
reaches s but not t. We have y<s, since sz is absent by the cover of
r with xs selected. The truncated cut at heads h>y exposes yz and
preserves r,wt, w reaching y, y reaching s, and (1). Apply (34)--(37)
or the selected-ys proposition, then undo the truncated cut. This
exhausts the cases and proves the corollary.

Thus the r-cover part of the retained-edge problem is now reduced to
redundant wt. More precisely, any nonzero source-component label
difference with r covering must have wt redundant; by the earlier
support result, f must be redundant at both endpoints too. This does
not settle cases with both outer anchors redundant or provide general
whole-component reassembly. Redundancy of the non-corner wt alone does
not justify deleting it from a whole component.

### Fixed checks

Related Rust: external `first_join_tree_lifts.rs`, option
`--retained-s-path`. Three fixed n10/n12 states have no selected ys,
a two-edge outgoing cut, competing prefix routes, redundant direct wy,
and an earlier incoming edge 3s. Their borrowed suffixes have lengths
one, three and two; the last also has an initially redundant yz and
an outer truncated cut. Every state explicitly verifies that the earlier
temporary long 3t is redundant with st present.

The paths have 15,19,19 flips. Every actual flip, strict edge and exact
endpoint passes the existing oracle; no state space is enumerated.
Sources, full edge lists and receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/retained-s-path-20260929/`.
The complete prior retained-edge text is preserved as a verbatim prefix.
No Lean/Lake build, worker, consultant, maintained Rust edit or independent
review was used. The general component e-expansion remains open.

## A covering interval across the incoming branch

2026-09-29 continuation. We treat further cases with redundant wt.
A different covering interval can carry a prefix to a vertex below t
that already reaches t. Its inverse tests end strictly below t, so
this preparation can be restored directly after the comparison.

**Proposition.** Keep the opening configuration S=Q+xs, T=Q+st.
Suppose there are vertices a,y,v such that

    w<=a<y<v<t<z,       x<y,
    r=xz, yz, av cover in S,
    a reaches y,       v reaches t.                 (38)

Then S~T with every other edge restored, with arbitrary exterior and
cycle rank. Neither wt nor a selected direct ay needs to cover; ay
may be absent. There is no condition on ys or on whether v reaches s
or z. The cover assumptions already exclude y=s and a=x.

If t reaches z, the earlier r-cover suffix theorem applies. If y
already reaches t, the earlier reachable-anchor theorem applies.
We may therefore assume neither of these paths exists initially.

### Remove the paths from v to z

Using the original S, list

    C={h : v<=h<z, hz selected, v reaches h},

where reachability from v to itself is allowed. Process C in decreasing
order, exchanging hz->yh while retaining yz. Each hz covers at its
turn: a bypass would end at a larger selected kz reachable from v,
already removed. The current cover of yz makes the flip actual and
is preserved. All new edges start at y<v, so reachability from v below
z is unchanged. At the end v does not reach z.

The cover of r persists. Initially x cannot reach y, because r covers
and yz is selected. New edges start at y and cannot create such a path,
so none of the new yh can bypass r. Likewise s cannot reach y: that
path, preceded by the selected xs and followed by yz, would bypass r.
Thus the new edges preserve all three conditions (1), after omitting xs.
Reachability from v to t and from a to y is unchanged. No cut step
creates a path from t to z, since its new tails lie below t.

If the cut creates a y-to-t path, apply the reachable-anchor theorem
immediately; r and yz still cover. The inverse cut is justified below.
Otherwise every new yh has h>v. Indeed, processing h=v would add yv
and hence a y-to-t path. All added heads therefore exceed v, and the
cover of av is preserved. We now have (38) together with v not reaching z.

### Move a prefix inside av

Choose a saturated selected path

    a=b_0 < b_1 < ... < b_m=y.

Successively exchange

    b_i b_(i+1) -> b_(i+1)v [retain b_i v],
    i=0,...,m-1.                                    (39)

The first retained long is the covering av. Each flip supplies the
next covering long, while earlier added edges end above y and cannot
spoil a prefix-short cover. At the end yv covers and y reaches t.
Earlier temporary longs need not remain covering between their uses.

The edge yz remains covering because the only new edges end at v,
which does not reach z. The edge r also remains covering. No original
prefix vertex b_i is reachable from x or s: its suffix to y and the
selected yz would contradict the cover of r, using xs in the latter
case. New edges end above every prefix vertex, so this remains true.
Consequently (39) preserves r and all the conditions (1).

Apply the earlier reachable-anchor theorem with the covering yz and
the newly selected y-to-v-to-t path. It replaces xs by st and restores
the entire prepared exterior. Now undo (39). Every tested interval is
contained in [a,v], with v<t; the new st cannot occur on any such path.
Removing xs can only help covers, and xs is not a tested edge, since
a prefix through x would contradict the cover of r with yz selected.
Every inverse is actual, restoring the full prefix.

Finally undo the incoming cut in reverse order, in either branch of
the proof. Compared with its recorded states, xs is removed and st
added. A bypass of yz or hz using st would require a t-to-z suffix,
which is still absent. A bypass of a tested yh would require t to
reach h. But hz was originally selected, so an original t-to-h path
would contradict t not reaching z. The cut only adds edges starting
at y<t, and hence never changes reachability from t below z. Thus
these bypasses are also impossible. All inverse flips are actual.
This proves the proposition, restoring every edge other than xs.

All exchanges are normal: the incoming cut lies inside yz and the
prefix moves lie inside av. Both are selected natural edges. The
full exterior is retained in every cover and reachability argument.

For a one-edge prefix, (39) is the single fork flip ay->yv [av].
This is the smallest instance of the proposition. The argument also
explains why we do not need to move ys first. Doing so can make yz
redundant after the fork flip when v reaches s; (39) avoids that step.

### Scope and fixed checks

The proposition supplies further repairs when wt is redundant, including
arbitrary prefixes and redundant ys. Outside this criterion, the remaining
r-cover cases still need another preparation or a coefficient correction.
We have not shown that every selected path from w to t provides an
interval av with a reaching the desired y. General whole-component
reassembly and the unrestricted left comparison remain open.

Related Rust: external `first_join_tree_lifts.rs`, options
`--retained-covering-fork` and `--retained-covering-interval`.
Four fixed n8/n10 fork paths have 7,7,7,9 flips, including a branch v
that reaches s and a two-edge v-to-t path with vt absent. Two fixed n12
states have redundant wt, redundant direct wy and redundant ys. One
uses an incoming cut followed by a three-edge prefix (13 flips); in
the other, the cut itself creates y-to-t and makes av redundant, so
the direct reachable-anchor branch applies (9 flips).

Every actual flip, strict edge and exact endpoint passes. No state
space is enumerated. The receipt also retains a failed earlier test
of unnecessary ys parking; that construction is not used here.
Sources, full edge lists and receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/retained-covering-fork-20260929/`.
The complete prior retained-edge note remains a verbatim prefix. No
Lean/Lake build, worker, consultant, maintained Rust edit or independent
review was used. The general component e-expansion remains open.

## Advancing a common ancestor and completing the r-cover case

2026-09-29 continuation. We remove the need to find a suitable covering
interval in advance. Local fork flips move a common ancestor of the
incoming branch and t forward until such an interval appears, or until
we obtain a covering edge ending at t. All these fork tests end below t,
so their inverses survive the final replacement of xs by st.

### A covering edge ending at t from another prefix vertex

**Lemma.** Keep the opening conditions and suppose

    w<=a<y<s<t<z,       x<y,
    r=xz, yz, at cover in S=Q+xs,
    a reaches y,       y reaches s,
    t does not reach z.                              (40)

Then S~Q+st with every other edge restored. The original wt may be
redundant, and no selected ys or direct ay is required.

Use exactly the outgoing cut and temporary-tz constructions of (30)--(37),
starting their saturated prefix at a instead of w. We justify this change
of starting vertex explicitly. The cut still retains yz and only adds
edges ending at z>t, so it preserves the cover of at and the whole
interval at or below y. Thus we still have a selected a-to-y path.
Such a prefix cannot use x, because r covering with yz selected excludes
any x-to-y path. This replaces the earlier use of x=w+1. The prefix
exchanges lie inside the covering at, and each new short supplies the
next retained long, just as before. They preserve r and yz: no prefix
vertex can be reached from x, and t does not reach z.

If ys is selected, first expose it and use (32), undo the a-to-y prefix,
then use (33) and undo the cut. During the inverse prefix both added
edges end at z>t, outside all tested intervals in [a,t]. If ys is absent,
the same nonempty outgoing cut supplies its last covering vz and a
remaining v-to-s suffix. Use (35)--(37), undo the prefix while st is
absent, restore st, and undo the suffix and outgoing cut. Suffix tests
start above y, so the restored prefix cannot affect them. The absence
of a t-to-z suffix still justifies the final outgoing-cut inverse.
These are precisely the previous cover arguments; none of their other
steps uses the identity of the initial prefix vertex. All exchanged
edges are normal inside at, yz or r. This proves (40).

### Two branches with a common ancestor

**Proposition.** Keep the opening conditions and suppose

    x<y<s<t<z,
    r=xz and yz cover in S=Q+xs,
    w reaches y,       y reaches s,
    t does not reach z.                              (41)

Then S~Q+st with arbitrary exterior and every other edge restored.
No cover of wt is required. Since wt is selected, w also reaches t.
If y reaches t, the earlier reachable-anchor theorem already applies.
We may therefore assume y does not reach t.

We maintain a vertex a with w<=a<y that reaches both y and t, beginning
at a=w. Choose saturated selected paths from a to y and from a to t.
Let their first edges be ab and av, respectively. Both cover, with

    a<b<=y,       a<v<=t.

If v>y and v<t, the covering-interval proposition (38) applies with
this a,y,v. If v=t, apply (40) using the covering at. The case v=y
is impossible because y does not reach t. It remains to explain how
to advance a when v<y.

If b=v, simply replace a by b; no edge changes. Otherwise make the
single actual fork flip

    ab -> bv [retain av],     if b<v,
    av -> vb [retain ab],     if v<b.                (42)

Both retained long and removed short cover. The new short is absent
by the long-edge cover, so the flip is actual. Its new tail
m=min(b,v) reaches both y and t: its original suffix to one endpoint
is untouched, and the new short leads to the other branch. Replace
a by m. In all cases the new a is strictly larger and still below y.

We check all the invariants in the full relation. Before (42), neither
x nor s can reach b: its suffix to y, followed by yz, would bypass r,
using xs first in the latter case. Neither x nor s can reach v either,
because v reaches t and the opening conditions exclude x-to-t and
s-to-t even in S=Q+xs. Thus the new short starts at a vertex unreachable
from x and s. It preserves r covering and all three conditions (1)
after omitting xs. Both changed edges start below y and end at or below
y, so they do not change any path starting at y or at t. In particular
yz still covers, y still reaches s but not t, and t still does not
reach z. The original recurrence edges, including wt, stay selected.
No fork creates q or g: its new tail exceeds w and its head is at most
y<t. The edges xs and st keep their original status during preparation.

The vertex a increases in the finite interval [w,y). Therefore this
procedure must stop in one of the two cases v>y. At that stage apply
(38) or (40), replacing xs by st and restoring the full prepared state.
Then undo every recorded fork flip in reverse order. Every tested
interval of (42) ends at or below y<t, so the new st cannot occur on
a tested path. Removing xs can only help covers and removes no tested
edge: each tested tail is either a or one of b,v, and none can be x
by the reachability exclusions just proved. Every inverse is actual.
Pure advances of a require no restoration. All original edges except
xs are restored, and st is inserted. This proves (41).

The fork flips are normal because the exchanged edges are proper shorts
of the selected natural long ab or av. The construction imposes no
uniqueness of either saturated path and no cycle-rank bound.

### Every comparison with r covering

**Theorem.** Under the opening Q conditions, if r covers in Q+xs,
then Q+xs~Q+st, with no additional hypothesis on the exterior.

If t reaches z, use the earlier selected-suffix theorem. Otherwise
form the original sets I,B. If B is empty, (C1) applies vacuously.
If B is nonempty, let y be its largest member. When y reaches t,
use the earlier truncated-cut/reachable-anchor theorem. In the remaining
case y reaches s but not t, and y<s: equality would require the selected
sz, impossible with r covering and xs selected.

Apply the truncated incoming cut at heads h>y. It exposes yz, preserves
r and (1), and leaves w reaching y and y reaching s. The selected wt
still gives w a path to t; its cover status is irrelevant. We now have
(41). Apply it and undo the truncated cut by its previously proved
inverse argument. This exhausts all cases and proves the theorem.

Together with the earlier f-cover proposition, every retained-edge
comparison with EITHER f or r covering in Q+xs is now repaired.
Consequently a nonzero source-component label difference forces both
f and r redundant at Q+xs, and the earlier endpoint argument also forces
f redundant at Q+st. We do not claim r must be redundant at Q+st.
The source r is generally a normal edge, so its redundancy does not
justify a whole-component corner deletion.

This closes the r-cover part of the unrestricted retained-edge problem.
The case with both original outer anchors redundant, the unrestricted
left comparison, and simultaneous whole-component reassembly remain open.
We do not infer the general e-expansion theorem from this local result.

### Fixed checks

Related Rust: external `first_join_tree_lifts.rs`, option
`--retained-common-ancestor`. Three fixed n12 states have redundant wt
and explicitly have no initial covering interval of type (38) for
their y=6. Each uses both orders in (42), moving the common ancestor
from 1 to 3 to 4. The first then uses a covering interval ending at
v=7<t=9, together with an incoming cut. The other two use (40), with
the covering 49 replacing the redundant original 19.

The terminal examples have respectively redundant selected ys and no
selected ys, as well as a competing direct a-to-s route. Both verify
that at becomes redundant with st selected, so the temporary-tz order
is necessary for their displayed inverse prefix. The three full paths
have 15,15,17 flips. Every actual flip, strict edge and exact endpoint
passes the existing oracle; no state space is enumerated.
Sources, full edge lists and receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/retained-common-ancestor-20260929/`.
The entire prior retained-edge note is a verbatim prefix. No Lean/Lake
build, worker, consultant, maintained Rust edit or independent review
was used. The general component e-expansion remains open.

## A lower bypass when both outer anchors are redundant

2026-09-29 continuation. We now work beyond the general r-cover theorem.
The following row allows r to remain redundant even after xs is deleted.
It uses the wx sector temporarily and restores a selected lower branch xa.
We also record the shorter-endpoint suffix observation used by the first
fixed comparison in this continuation.

### A shorter covering edge from x

If t<v<=z, xv covers in S, and t reaches v, then S~T regardless of
whether wv is selected. Apply the earlier covering-r/selected-suffix proof
with v in place of z: borrow xt backwards along a saturated t-to-v path,
exchange xs->st retaining xt, and undo the path preparation. This proof
uses only the covering xv, the selected suffix and (1); it never retains
wv or the original f. All tested intervals lie in [x,v], and all changed
edges are normal inside the original natural corner wz. A suffix of
length m gives 2m+1 flips. In particular, covering xv,tv give

    tv -> xt [retain xv],
    xs -> st [retain xt],
    xt -> tv [retain xv].

Both original outer anchors can be redundant throughout this row.

### Seven flips through a lower branch

**Proposition.** Keep the opening Q conditions, and suppose x<a<s with

    ws, wt, xa, az, sz, tz cover in S=Q+xs.           (43)

Suppose also that either w does not reach a, or wa is selected and
covers. Then S~T in seven actual flips, restoring every other edge.
The exterior and cycle rank are arbitrary.

Here f and r are both redundant in S, through ws,sz and xs,sz.
Moreover r remains redundant in S-xs through xa,az. Thus the proposition
does not follow from the earlier rows that assume r covers after xs is
deleted. By (1) and the selected xa, neither a-to-s nor a-to-t is a path
in Q. In particular as and at are initially absent.

First suppose w does not reach a. We use the four-flip preparation

    xa -> as [retain xs],
    xs -> wx [retain ws],
    as -> wa [retain ws],
    wx -> xa [retain wa].                            (44)

The first flip is actual because xs covers by (1), and xa covers by
(43). The new as cannot bypass ws, since w does not reach a. Thus the
second flip is actual and supplies a covering wx. Its added edge starts
below a and cannot affect the cover of as, while the flip preserves
ws covering. The third flip is therefore actual and supplies a covering
wa. The fourth uses this new covering long and the covering wx. It
restores xa. The state after (44) is exactly Q+wa.

The edge wt covers in Q+wa: removing xs only helps its original cover,
and a new bypass through wa would require the forbidden a-to-t path.
The new wa covers by (44). Exchange

    wa -> at [retain wt].                            (45)

We have reached Q+at, with at covering. Finish with

    tz -> st [retain sz],
    at -> tz [retain az].                            (46)

The covers of sz and tz are unchanged before the first flip, since
all preceding changes start below s or t respectively. This flip removes
tz and creates st as a cover. Removing the covering tz leaves no t-to-z
path; adding st cannot create one. Also a still does not reach s.
Consequently neither the new at nor st can bypass az. Its original
cover has returned, although at,tz made it redundant just before (46).
The edge at still covers: a new bypass using st would require a-to-s.
Thus the last flip is actual, restores tz, removes at and leaves Q+st.
This proves the first case.

If wa is already selected and covering, perform (45) FIRST. It is
actual by the original covers of wa and wt. Removing the covering wa
leaves w not reaching a; the new at cannot change this. The covers of
ws,xs,xa are preserved, because the added head t exceeds s and a.
We may therefore use all four flips (44) in this prepared relation.
They restore the original wa and xa and remove xs. The resulting state
is again Q+at, now with the originally selected wa present in Q.
Use (46) exactly as before. Restoring wa may make wt redundant, but
we do not retain wt after that restoration. This proves the second case.

All exchanged edges are proper shorts of selected natural edges inside
wz, hence normal. The proof neither assumes an isolated local diagram
nor discards an exterior edge during a cover test.

### Scope and fixed checks

The condition on wa is substantive: a longer w-to-a path, or a selected
redundant wa, does not automatically satisfy either case. We have not
proved that such routes can always be prepared while preserving the
needed covers. Redundant members of (43), and the general both-redundant
comparison, also remain open. Whole-component reassembly is separate.

Related Rust: external `first_join_tree_lifts.rs`, option
`--retained-lower-bypass`. One fixed n7 and two fixed n11 states pass
seven-flip paths. The n11 states have extra shared descendants and
redundant normal edges; one also has the initial covering wa. All three
verify both original anchors redundant and r still redundant after
xs deletion. Every actual flip, strict edge and exact endpoint is checked.
No n11 state space is enumerated.

The discovery option `--retained-both-redundant-fixed` checks only two
fixed n7 pairs. Its bounded paths visit 90 and 919 states and have three
and seven flips, respectively. The first is the shorter-endpoint suffix
row, and the second is (44)--(46). These finite checks prompted the
arbitrary-exterior arguments above; they are not an exhaustive coverage
claim. Sources, full edge lists and receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/retained-both-redundant-20260929/`.
The entire prior retained-edge note remains a verbatim prefix. No Lean/Lake
build, worker, consultant, maintained Rust edit or independent review
was used. The general component e-expansion remains open.

## Preparing an arbitrary lower prefix inside ws

2026-09-29 continuation. We can allow arbitrary w-to-a routes and a
redundant wa if deleting xs and xa exposes r. This condition is separate
from the hypotheses of (43); unlike that proposition, we need no cover
or even selection of az. We make the entire prefix preparation inside
[w,s], so that its inverse is unaffected by the final change above s.

**Proposition.** Keep the opening Q conditions and suppose x<a<s with

    ws, wt, xa, sz, tz cover in S=Q+xs,
    w reaches a,
    r covers in Q-xa.                                (47)

Then S~T with arbitrary exterior and every other edge restored. The
edge wa may be absent, covering or redundant, and its longer paths
may have arbitrary competing branches.

First exchange

    xs -> wx [retain ws],
    wx -> xt [retain wt].                            (48)

The first flip uses the covers of xs and ws. After it, x has no path
to t: removing xs leaves Q, and the new wx starts below x. Thus wx
cannot bypass wt, making the second flip actual. We reach B=Q+xt,
with xt covering. The covers of ws,xa,sz,tz are preserved by the
ordering of their intervals and the absence of wx at this endpoint.

### Expose or create wa below s

In increasing order process all selected wb with w<b<a and b reaching
a in B, exchanging wb->bs while retaining ws. Each wb covers at its
turn by the first-edge argument. The cut preserves ws covering and
removes every w-to-a path except the direct wa, if selected.
All added heads s exceed a. The cut therefore preserves xa covering.
Also b cannot equal x, since wx is absent in B, so every processed
head b exceeds x.

If wa is selected, it now covers and this is the whole preparation.
If wa is absent, the cut is nonempty. Let b be its largest processed
head. The final cut flip supplies a covering bs, and b still reaches a.
Along a saturated b-to-a path, successively exchange

    v_i v_(i+1) -> v_(i+1)s [retain v_i s].

Each new short supplies the next covering long, ending with as. Earlier
added edges end above a and cannot affect a path-short cover. The edge
ws remains covering: w cannot reach any path vertex, since such a path
would reach a, which the outgoing cut has made impossible. Now exchange
as->wa, retaining ws. This creates a covering wa and removes the
temporary as. Denote the complete cut and suffix preparation by P.

Every interval tested by P is contained in [w,s]. At its endpoint, all
new edges other than wa have the form bs with x<b<a, where b originally
reached a. The original cover of xa excludes an x-to-b path: it would
provide an alternative x-to-a path. None of the preparations creates one,
since all its new heads are at or above a and wa starts below x.
In particular, x has acquired no path to s at the endpoint of P.
The transient as in the absent-wa construction has been removed.

### The central row and full restoration

In this prepared state use

    xa -> wx [retain wa],
    tz -> st [retain sz],
    xt -> tz [retain r],
    wx -> xa [retain wa].                            (49)

The first flip uses the exposed wa and preserved xa covers. The second
uses sz and tz; no preceding change can affect a path starting at s or t.
Removing the covering tz leaves no t-to-z path.

For the third flip, r now covers. The original Q-xa has r covering by
(47). The preparation's new bs are unreachable from x, and wa and wx
start below x. The added xt has no t-to-z suffix, and st cannot give a
bypass because x does not reach s. These observations exclude every
new x-to-z bypass. The edge xt also covers: the only newly possible
bypass after st was inserted would require x reaching s. Thus the third
flip is actual. The fourth restores xa, using covers whose tests lie
inside [w,a], below all changes made by the middle two flips.

Relative to the endpoint of P, (49) removes xt and adds st, restoring
xa and the absence of wx. Both changed edges end at t>s. Consequently
neither affects ANY interval tested by P, all of which lie in [w,s].
Every inverse flip of P is actual. We restore the complete original
lower prefix, including the original status of wa, and finish at Q+st.
This proves the proposition with 2|P|+6 flips. All exchanged edges are
normal inside the selected natural longs ws,wt or r.

The cover of r after deleting both xs and xa is substantive. Other
x-to-z bypasses may survive those deletions, and (47) does not cover
that case. Conversely (43) can allow such additional bypasses, so the
two propositions provide different sufficient conditions.

## Extending xs to xt along an arbitrary lower prefix

The same preparation gives a useful intermediate transfer with no outer
anchor hypothesis.

**Lemma.** Under the opening Q conditions, if wt covers in Q+xs and
w reaches s, then

    Q+xs ~ Q+xt,                                     (50)

with every other edge restored. The edge ws may be absent or redundant.
This moves the edge starting at x; it does not assert the previously
refuted transfer wt->xt.

Prepare a covering ws using the construction above with the target a
replaced by s and the containing endpoint s replaced by t. Explicitly,
cut every proper outgoing wb with b<s and b reaching s, using wb->bt
while retaining wt. If ws is selected, the cut exposes it. Otherwise
take the last new bt, carry it forward along a saturated b-to-s suffix,
and exchange the resulting st for ws, retaining wt. The cut has removed
all w-to-s paths before this last flip, so wt stays covering throughout.
Call this preparation P_t.

The original cover of xs excludes x reaching any prepared suffix vertex
below s. All new edges ending at t therefore have tails unreachable from
x, except the temporary st, which is removed before the central row.
The edge xs still covers, and there is no x-to-t path after xs is omitted.
Use (48), now with the prepared ws, to replace xs by xt.

We can undo all of P_t while keeping xt selected. A new bypass of its
retained wt through xt would require w reaching x. This is impossible:
w,x are adjacent, wx is absent, and no preparation or inverse introduces
it. Every other tested edge ending at t has tail strictly above x and
hence cannot use the new xt. All tested edges with smaller heads end
at or below s<t, so cannot use it either. Removing xs only helps covers and removes no tested
edge, since no suffix vertex equals x. All inverses are actual and restore
the original ws and its entire prefix. This proves (50) with 2|P_t|+2 flips.
No original strict corner is changed.

### A consequence with r covering after xs deletion

Suppose, in addition to the hypotheses of (50), that r covers in Q and
sz,tz cover in Q+xs. After (50), finish with

    tz -> st [retain sz],
    xt -> tz [retain r].                             (51)

The first flip uses the unchanged sz,tz covers. Then t does not reach z,
and x does not reach s. Thus the added xt and st cannot bypass the
originally covering r in Q, making the second flip actual. The final
relation is Q+st. This gives a retained-edge repair with arbitrary
w-to-s routes and no selected or covering ws assumption. It uses
2|P_t|+4 flips. Both original outer anchors can be redundant in Q+xs.

### Fixed checks and remaining cases

Related Rust: external `first_join_tree_lifts.rs`.
`--retained-lower-prefix` checks four fixed n8/n12 paths of 12,8,16,10
flips under (47). They have absent or redundant wa. The n12 states have
competing routes and redundant az, and the absent-wa case uses a two-edge
suffix after its outgoing cut. `--retained-short-extension` checks (50)
and (51) separately in two fixed n12 states with absent or redundant ws.
Their extension paths have 12,6 flips and their complete retained-edge
repairs have 14,8 flips. Every actual flip, strict edge and exact endpoint
passes. No n12 state space is enumerated.

The discovery option `--retained-lower-prefix-fixed` checks only two fixed
n8 comparisons. It visits 15046 and 11937 states and finds eight-flip
paths, with absent and redundant wa respectively. The general construction
need not give a shortest path. Sources, full edge lists and receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/retained-lower-prefix-20260929/`.

The general both-redundant comparison remains open when the stated
post-deletion covers or the containing/suffix covers fail. The unrestricted
left comparison and whole-component reassembly are still separate tasks.
The entire prior retained-edge note remains a verbatim prefix. No Lean/Lake
build, worker, consultant, maintained Rust edit or independent review
was used. The general component e-expansion remains open.

## An absent tz with arbitrary paths from t to z

2026-09-29 continuation. We remove the suffix-cover condition from (51)
when tz is absent, without assuming that t does not reach z.

**Proposition.** Keep the opening Q conditions. Suppose

    wt covers in S=Q+xs, and w reaches s;
    r=xz and sz cover in Q;
    tz is absent.                                   (52)

Then S~Q+st with arbitrary exterior and every other edge restored.
The edge ws may be absent or redundant, and t-to-z paths may have
arbitrary competing branches and redundant incoming edges at z.

First apply the short-extension lemma (50), reaching Q+xt and restoring
the entire lower prefix. Now apply the [background-anchor proposition](COMPONENT_RIGHT_ARM_TRANSFER.md#covers-in-the-background-and-an-absent-direct-suffix)
(A3) with

    (u,v,d,c)=(x,s,t,z).

Its two anchors cover in Q by (52), and Q has neither an x-to-t nor
an s-to-t path by the opening conditions. The direct suffix tz is
absent. Thus Q+xt~Q+st, proving the proposition. The intermediate r
may be redundant through xt and a t-to-z path; (A3) specifically allows
this. We do not use the earlier theorem requiring r to cover in S.

Combining (52) with (51), the same hypotheses on wt, w-to-s reachability
and the background covers r,sz now settle every suffix case except a
SELECTED REDUNDANT tz. These hypotheses do not assert the unrestricted
both-redundant retained-edge theorem. Other failures of the displayed
covers and the left comparison remain separate from this corollary.

Related Rust: external `first_join_tree_lifts.rs`, option
`--retained-absent-tz`, checks two fixed n12 states with absent/redundant
ws, several t-to-z paths, absent tz and an initially redundant incoming
edge at z. The short extensions take 10 and 6 flips; the subsequent
background-anchor transfer takes 16 in each. The complete repairs take
26 and 22 flips. Every actual flip, strict edge and exact endpoint is
checked; no state space is enumerated. Sources and receipts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/retained-suffix-covers-20260929/`.
The complete prior note remains a verbatim prefix. No Lean/Lake build,
worker, consultant, maintained Rust edit or independent review was used.
The whole-component reassembly needed for the general e-expansion is
still open.

## A redundant tz with covering proper incoming suffix edges

2026-09-29 continuation. The new shared-suffix arm construction settles
part of the selected-redundant-tz case left after (52).

**Proposition.** Keep the opening Q conditions. Suppose wt covers in
S=Q+xs, w reaches s, and r=xz and sz cover in Q. Suppose tz is selected,
and every selected hz with

    t<h<z and t reaching h in Q

covers in Q. Then

    Q+xs ~ Q+st.                                    (53)

The direct tz may be redundant. We allow arbitrary competing paths from
t to each proper incoming tail h, and arbitrary exterior subject to the
stated hypotheses. The edge ws may be absent or redundant.

Apply (50) to reach Q+xt and restore the lower prefix. Apply the
[selected-suffix background-anchor proposition](COMPONENT_RIGHT_ARM_TRANSFER.md#a-selected-direct-suffix-with-covering-proper-incoming-edges)
(A10) with (u,v,d,c)=(x,s,t,z). The opening conditions exclude both
x-to-t and s-to-t paths in Q, and the required two anchors cover there.
Its last-edge hypothesis is exactly the displayed assumption. Hence
Q+xt~Q+st, proving (53), with every other edge restored.

Together with (51) and (52), the remaining suffix case under these same
wt, w-to-s and background-anchor assumptions must have BOTH selected
redundant tz and a redundant proper incoming hz reachable from t.
Equivalently, two selected proper incoming tails are comparable by a
path in Q. This does not restrict the whole unresolved retained-edge
problem, where those earlier cover assumptions may also fail.

Related Rust: external `first_join_tree_lifts.rs`, option
`--retained-selected-suffix`, checks two fixed n12 states with redundant
tz, two incomparable proper incoming tails, competing paths, and absent
or redundant ws. The short extensions take 10/6 flips and the following
transfer takes 26 in both cases, for totals 36/32. Every actual flip,
strict edge and exact endpoint is checked; no state space is enumerated.
Receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/retained-selected-suffix-20260929/`.
No Lean/Lake build, worker, consultant, maintained Rust edit or independent
review was used. Prior text remains a verbatim prefix. The general left
comparison and whole-component reassembly remain open, and the requested
recurrence proof of component e-expansion is still incomplete.
