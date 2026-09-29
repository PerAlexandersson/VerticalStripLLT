# Moving an incoming edge with a selected containing interval

2026-09-28. We prove an incoming-edge transfer, including edges on the
unique cycle, when a suitable containing interval is already selected.
Primary and Astra independently audited the case split and cover tests.
The subsequent [incoming-edge induction](COMPONENT_NN_LEFT_REASSEMBLY.md)
handles arbitrary containing corners uv in the saturated NN setting when
the two exchanged incoming edges cover at their respective endpoints.

## Statement

Let G be any ordinary interval-closed natural graph with allowed strict
corners. Let A be a connected unicyclic selected state, and suppose

    t<a<b=a+1<v<c.

Write f=ac, r=bc and q=ab. Assume that A selects f,r,ta,tv, omits
q,tb, and that its unique cycle uses f or r.

**Theorem.** A and A−ta+tb belong to the same actual flip component.
Every other selected edge is restored at the endpoint.

We do not require NN eligibility, saturation, or strictness of f or tv.
Every exchanged edge below is a proper subinterval of f or tv, and
therefore is natural and cannot be a strict corner. We use the proved
[outgoing transfer](COMPONENT_RIGHT_ARM_TRANSFER.md) as a path replacing
av by bv while retaining f,r and restoring every other edge. Each use
of that theorem concerns a connected unicyclic state selecting f,r and
omitting q; it does not require the cycle still to use f or r.

## The first two cases

The unique cycle contains c. Therefore ta and tv cover: any bypass of
either would give the unique cycle entirely below c. Moreover av is
absent, since otherwise ta,tv,av would already form such a cycle.

Suppose first that bv is selected. Use

    ta → av, retaining tv;
    bv → tb, retaining tv;
    av → bv, by the outgoing transfer.

The initial unique cycle is t–a–c–b–v–t. After the first move it is
the four-cycle {f,r,av,bv}, with tv a bridge. Thus the second move
is actual. The outgoing theorem supplies the last path, and the
endpoint is A−ta+tb.

Now suppose bv is absent. Start with ta→av, retaining tv, and then
use the outgoing transfer av→bv. The resulting selected set is

    P=A−ta+bv.

If tv and bv both cover in P, finish with bv→tb, retaining tv.
This gives the theorem in this case. A unicycle has at most one
redundant edge, so there are just two possible failures of this last
flip. We repair each by changing one edge before the preceding path
and restoring it afterwards.

## When tv would become redundant

A bypass of tv in P must use the newly inserted bv. Hence the
original A contains a directed path

    t→x→...→b,       t<x<a.

The inequalities follow from the absence of tb and q. This path,
together with ta,f,r, is the unique cycle of A; tv is a bridge.
We use the following stages:

| Retained edge | Move |
| --- | --- |
| tv | tx → xv |
| tv | ta → av |
| f,r | av → bv, by outgoing transfer |
| tv | bv → tb |
| tv | xv → tx |

The first move breaks the t-to-b path. Its new xv is absent initially,
by uniqueness of the cycle, and the required edges cover. After the
outgoing-transfer endpoint, the unique cycle consists of xv, the
remaining x-to-b path, and bv. Only xv is redundant, while tv is
pendant and bv covers. Therefore the fourth stage is actual. It breaks
the bypass of xv, so the last flip is actual as well. The final tb
is redundant, but it is not used in a cover test. All original path
edges and every exterior attachment are restored.

## When bv would become redundant

A bypass of bv in P is an original directed path

    b→x→...→v,       b<x<v.

Together with ta,f,r,tv, it gives the unique cycle of A. Use

| Retained edge | Move |
| --- | --- |
| r | bx → xc |
| tv | ta → av |
| f,r | av → bv, by outgoing transfer |
| tv | bv → tb |
| r | xc → bx |

Initially the cycle edges cover. The first move breaks the b-to-v
path and makes r a bridge. After the outgoing-transfer endpoint,
the cycle consists of r,bv,xc and the remaining x-to-v path; tv is
pendant, and bv covers. The fourth stage is therefore actual. The
edges r and xc still cover afterwards, so the final flip restores bx.
It makes tv redundant only in the final state, when tv is no longer
used as a retained cover.

These cases exhaust the possibilities and prove the theorem. All
exterior edges belong to trees attached singly to the displayed cycle
and branches, so they do not alter the cover tests.

## Verification and remaining scope

The existing actual-flip consumer checks all four constructions on the
eligible NN instances through six vertices. The respective case counts
are 19,36,1,1; in particular both bypass repairs are exercised. The
seven-vertex shield fixture adds 20,57,4,0 instances. Every individual
nonmacro flip is checked by its actual cover conditions. Each outgoing
macro is checked by membership of its endpoints in the same full
component, in addition to the separate uniform outgoing-transfer proof.
These finite checks support the local proof; the theorem is not limited
to the NN instances used in this test.

Related Rust: external `nn_component_transport.rs`, modes
`--audit-incoming-cycle --audit-selected-tv`. Frozen sources and receipts
are under `/lake-cache/ai-projects/requests/VerticalStripLLT/incoming-transfer/`.
No new polynomial generator, Lean declaration or manuscript change is claimed.

A saturated NN diagram supplies a selected containing corner uv with
u≤t<a<b<v<c. The theorem applies directly when u=t, or whenever tv
is otherwise selected. It does not justify inserting tv when u<t.
The previously proved incoming-bridge result covers arbitrary containing
corners, but its proof does not apply to an edge on the cycle.

## Three covering anchors: arbitrary exterior and cycle rank

2026-09-29 continuation. We replace the unicyclic assumption by explicit
cover conditions and give a path restoring the full exterior. The argument
does not assume any component polynomial identity. The independent audit
recorded above predates this continuation and does not cover it.

Let t<w<x<d<z. We do not require w,x to be adjacent. Suppose a selected
state S contains

    f=wz,  r=xz,  g=td,  p=tw,

all four as covers, and omits p'=tx. Then

    S ~ S-tw+tx.                                      (12)

All other selected edges are restored, and f,r still cover at the endpoint.
The containing edge g need not be strict or maximal; nor need f,r.
All exchanged shorts below lie properly inside a selected natural long,
so they are natural and cannot be strict corners.

We use three preparations. Their order matters for restoring the exterior.
Initially w cannot reach x, because f covers and r is selected. Also w
cannot reach d, because g covers and p is selected.

### First clear t-to-x paths

In increasing order process

    I={v : t<v<x, tv selected, v reaches x},

using tv -> vd, retaining g. The vertex w is not in I, since w cannot
reach x. Every processed tv covers: a bypass starts with an earlier
selected outgoing edge whose head also reaches x, already removed by the
sweep. New edges end at d>x and cannot restore such a path. The covering
g makes each exchange actual and remains a cover.

The anchors f,r remain covers too. A new bypass of f using vd would
require w to reach v and then x in the original relation, contradicting
w not reaching x. A path starting at x cannot use a new vd with v<x.
The edge p still covers, because all added edges end above w. This sweep
clears every t-to-x path and leaves reachability starting at x or d
unchanged.

If I is nonempty, the original state had a t-to-x path. The original
cover of g then implies that x did not reach d. We retain this fact
for the final restoration; we do not assume I is empty.

### If necessary, borrow xd while preserving r as a cover

If d does not reach z, skip this preparation. Otherwise form

    J={v : d<=v<z, vz selected, d reaches v}.

Process J in decreasing order, replacing vz by xv while retaining r.
Each vz covers when processed, because a bypass would end in a later
uz already removed. The cover of r excludes an existing x-to-v path.
Thus all exchanges are actual and preserve r as a cover. Their added
edges start at x, which w cannot reach, so f remains a cover. Their heads
are at least d and t cannot reach x, so g remains a cover. They do not
affect p or any reachability below x.

The sweep clears all d-to-z paths. More generally, no vertex reachable
from d below z can still reach z: otherwise d could follow that route.
Let v be the smallest element of J. The new xv covers. Before the sweep
there was no x-to-v path, by the original cover of r and selected vz;
every other new outgoing edge at x ends above v.

Choose a saturated selected path d=v_0<...<v_m=v. Working backwards,
replace v_i v_(i+1) by xv_i, retaining xv_(i+1). These are actual flips:
the retained long covers, each path edge covers, and the newly selected
short supplies the next retained long. Added edges start below d, so
they cannot spoil a remaining path-edge cover. At the end xd is selected
and covers. The case v=d needs no path flips.

The edge r remains a cover throughout this borrowing, not merely at its
first step. Every new xv_i ends at a vertex reachable from d, whose
routes to z were all cleared by the incoming sweep. The other anchors
f,g and the arm p remain covers for the same ordering reasons as before.
This stronger preservation is why we cleared the entire incoming cut
before borrowing along one chosen path.

### Clear alternative x-to-d paths

In increasing order process every selected xv with x<v<d and v reaching d,
replacing xv by vz while retaining r. The first-edge argument again proves
every flip actual and leaves r covering. The new vz cannot bypass f:
w reaching v would imply w reaching d, excluded by g and p. It cannot
affect g or p, whose heads lie below z.

We now have no x-to-d path except possibly the direct edge h=xd. If
selected, h covers. The anchors f,r,g and p still cover; t does not
reach x; and d does not reach z. Every other temporary edge is recorded
for later restoration.

### A four-flip central row

Use the appropriate row, where the brackets specify the retained long:

| Status of h=xd | Actual flips |
| --- | --- |
| Absent | tw -> wd [g]; wd -> dz [f]; dz -> xd [r]; xd -> tx [g] |
| Selected | xd -> tx [g]; tw -> wd [g]; wd -> dz [f]; dz -> xd [r] |

For the g-retained flips, the selected shorts cover by the preparations
and the preceding actual flip. The absence of t-to-x and of alternative
x-to-d paths supplies the needed covers of g. The f-retained flip is
actual because d does not reach z. Its added dz does not bypass r,
since there is no x-to-d path at that stage. Thus the r-retained flip
is actual as well. Each row replaces p by p', restores the initial
status of h, and leaves both f and r covering. In the second row g may
be redundant at the endpoint, where it is no longer used.

### Restore the preparations in reverse order

First undo the outgoing x-cut and then the borrowing preparation, if used.
Every tested edge in these preparations starts at x or later. Relative
to the forward stage, p=tw has been removed and p'=tx added. Both have
tail t<x, so neither can lie on a directed path starting at a tested tail.
All corresponding cover tests are therefore unchanged, and every inverse
flip is actual.

It remains to undo the initial g-retained sweep. If it was nonempty, we
proved that x could not reach d in the original state. The later
preparations have now been undone, and the initial sweep does not change
reachability starting at x. Thus adding tx cannot bypass g. It cannot
bypass a tested tv, whose head is below x, or a tested vd, whose tail
is above t. Removing tw cannot spoil a cover. All inverse flips are
actual. Every exterior edge is restored, proving (12).

The construction uses four central flips and twice the number of
preparation flips. There is no connectedness or cycle-rank assumption.
It does not assert a transfer when one of f,r,g,p is redundant.

## A DN left-overlap consequence

Use the DN notation u<t<w<x<z with x=w+1, e=uw, f=wz, r=xz,
and e'=ux. Suppose an actual target flip retaining e' exchanges ut,tx
in sector 10. Let its corresponding source states be

    A=L01(Q+ut),       B=L01(Q+tx).

Assume e,f,r cover in A. The selected ut covers because the target
flip is actual and the corner change cannot affect its interval.
Therefore ut -> tw [retain e] is an actual source flip; write its
endpoint A*. Adding tw cannot affect covers of f or r, since its tail
lies below w.

If A* has a selected covering g=td with x<d<z, all four covers required
in (12) hold in A*: tw is the new short in an actual flip. Applying
(12) gives A* ~ B, hence A ~ B. For every source component indicator h,

    h01(Q+ut)=h01(Q+tx).                              (13)

Thus the direct t10 coefficient is constant on this target comparison.
The [opposite-defect identity](COMPONENT_DN_DIRECT_OVERLAPS.md#the-00-comparisons-follow-the-10-comparisons)
also settles its corresponding actual 00 comparison. This uses membership
in an actual component, not a claim that K or E is invariant on one flip.

At a SATURATED genuine DN first-drop contact, the required edge td is
present automatically for every u<t<w: earlier strict corners have tails
0,...,w-1, their heads increase with their tails, e has head w, and row x
is nonstrict. The corner with tail t consequently has x<d<z. This is
the [corner description in the coverage proof](COMPONENT_RECURRENCE_COVERAGE.md#the-first-drop-lemma).
Its cover in A* is not automatic. Even if td covers in A, insertion of
tw can make it redundant through a w-to-d path. We handle two further
classes below. The selected but unmarked upper corner in a DD-derived
DN step also needs its own treatment.

### A path to d on only one side

We can replace the assumption that td covers after the e-retained flip
by the following condition on the original A:

    e,f,r,g cover in A, and w,x do not BOTH reach d.    (14)

Here g=td remains selected and x<d<z. If w does not reach d, the first
e-retained flip leaves g covering and the preceding argument applies.

Suppose instead that w reaches d and x does not. The cover of f implies
that d cannot reach z. In increasing order, replace every selected wv
with w<v<d and v reaching d by vz, retaining f. Each wv covers at its
turn, by the first-edge cut argument. The new vz cannot bypass r because
x reaching v would imply x reaching d. It cannot affect g,e or ut, whose
heads lie below z. Thus all required covers persist, while every
w-to-d path except possibly the direct h=wd is cleared. The edge h
covers if selected. No t-to-x path exists: the original actual target
flip, with ut selected, excludes it, and preparation adds no edge with
head at most x.

Use one of the following five-flip rows:

| Status of h=wd | Actual flips |
| --- | --- |
| Absent | ut -> tw [e]; tw -> wd [g]; wd -> dz [f]; dz -> xd [r]; xd -> tx [g] |
| Selected | wd -> dz [f]; dz -> xd [r]; xd -> tx [g]; ut -> tw [e]; tw -> wd [g] |

The cleared w-to-d and x-to-d paths supply the covers in the g-retained
steps. The absence of d-to-z paths supplies the f-retained step and the
absence of x-to-d paths supplies the r-retained step. The e-retained step
is unaffected by changes ending above w. The newly inserted shorts cover
after each actual flip. Thus both rows are actual; each restores h and
replaces ut by tx.

Finally undo the w-cut. Its tested edges all start at w or later, whereas
both the removed ut and added tx have tails below w. The cover tests are
unchanged, so every inverse flip is actual. This proves (13) under (14),
even when g would have become redundant immediately after inserting tw.
For k preparatory edges in this second case, the path has 2k+5 moves.

### A direct common branch, allowing both outer anchors to be redundant

There is also a four-flip repair with different hypotheses. Assume the
original source A selects wd,xd and that

    e=uw,  g=td,  wd,  xd,  ut all cover.             (15)

We keep the actual target comparison and its absent q=wx and tx.
We make NO cover assumption on f=wz or r=xz. Then use

    xd -> tx [retain g],
    ut -> tw [retain e],
    tw -> wx [retain tx],
    wx -> xd [retain wd].                            (16)

The first flip is actual by (15), and its new tx covers. The change ends
above w, so the second flip is actual too. After inserting tw, a bypass
of tx would require a w-to-x path. This is impossible because x=w+1 and
wx is still absent. Thus the third flip is actual and its new wx covers.

For the last step, wd was a cover originally. The earlier changes delete
xd and ut and add edges starting below w, except for the new wx. A bypass
of wd using wx would require an x-to-d path after xd is removed. The
original cover of xd excludes that path, and changes below x cannot
create it. Hence wd still covers, and the last flip is actual. Every
edge except ut,tx is restored. This proves (13) under (15), including
states where both outer anchors f,r are redundant.

The two additional constructions again give direct coefficient constancy;
they do not add a signed correction. The remaining cases include common
descendant configurations whose short arms do not satisfy (15), and states
where e or the containing g fails the stated cover conditions. None of
these lemmas by itself proves unrestricted left reassembly or global
whole-component collection.

## Exact checks of the new paths

Related Rust: existing external `first_join_tree_lifts.rs`, functions
`incoming_anchor_path` and `incoming_move`, option `--incoming-anchor-check`.
Every flip uses the established full cover/flip oracle. The final selected
set and preservation of strict edges and the two outer covers are checked.

| Fixed natural area | (t,w,x,d,z) | Applicable states | Actual flips checked |
| --- | --- | ---: | ---: |
| 012233 | (1,2,3,4,5) | 6 | 28 |
| 012345 | (0,2,3,4,5) | 58 | 280 |
| 012345 | (0,1,3,4,5) | 40 | 196 |
| 012345 | (0,1,2,4,5) | 38 | 180 |

All 142 applicable instances pass. These include nonadjacent w,x,
nonmaximal anchors, a nonempty first cut, borrowing, and a nonempty
last cut. Two additional fixed ten-vertex states check a pair of
d-to-z suffixes (10 flips) and two bypasses of xd (8 flips); no
ten-vertex state space is enumerated.

The separate option `--incoming-left-check` checks (14) at all four
qualifying target comparisons from source area012233 to target012332
(22 source flips), and checks the two instances of (15) there (8 flips).
One of the latter has BOTH f and r redundant. Two further fixed states
check a w-to-d path with wd absent at n=8 (7 flips), and two bypasses of
selected wd at n=10 (9 flips). Their preparation verifies the case where
g would have become redundant after the naive e-retained first flip.

The earlier one-state `--left-common-branch-probe` found the four-flip
row (16); the proof above supplies its arbitrary-exterior justification.
The diagnostic does not use component membership as a replacement for
the constructed row. Finite checks support the written proof; no
unrestricted coverage claim or new independent review is made.

Sources, logs and the preserved before-file are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/incoming-anchor-20260929/`.
Maintained Rust sources, Lean sources and manuscript sources are unchanged.
No Lean/Lake build, new worker or consultant was used.
