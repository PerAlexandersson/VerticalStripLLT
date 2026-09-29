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
