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

## Clearing nonshared proper arms in the left DN comparison

2026-09-29 continuation. We strengthen the one-sided class (14), allowing
both w and x to reach d and allowing both direct arms wd,xd to be
redundant initially. This gives actual source paths, hence loops among
the corresponding equalities in the homogeneous DN completion theorem.
It does not settle all generators of that completion.

Keep u<t<w<x<d<z with x=w+1. Let A select

    e=uw, f=wz, r=xz, g=td, ut,

all as covers in A, and omit wx,tx. Assume t does not reach x. These
are the earlier covering-anchor hypotheses for a left DN comparison.
Define its proper outgoing cut at w by

    I={v : x<v<d, wv selected in A, v reaches d in A}.

**Proposition.** If xv is absent for every v in I, then

    A ~ A-ut+tx,                                      (18)

with every other selected edge restored. No condition is imposed on
whether wd,xd are present or covering, or on whether x reaches d.
The entire exterior remains in the cover and reachability tests.

First note that t cannot reach w: with ut selected, such a path would
bypass the covering e. The assumed absence of a t-to-x path and of wx
will also persist through the preparations below.

Process I in increasing order, transferring wv to xv by the proved
[two-covering-anchor construction](COMPONENT_RIGHT_ARM_TRANSFER.md#arbitrary-exterior-transfer-with-two-covering-anchors),
with roots w,x and common endpoint z. When v is processed, wv covers.
A bypass would start with an earlier outgoing wh, h<v, with h reaching
d; that h belonged to I and its edge wh has already been removed.
The added xy edges cannot create a new path from w, since w,x are
adjacent and wx is absent. The companion xv is still absent before its
own transfer. Thus every use of the covering-arm lemma is justified.

Each transfer keeps both outer anchors covering and restores all edges
apart from wv,xv. During its internal path, new edges either end at z>d
or are the final xv. The former cannot bypass g=td; the latter cannot
bypass g because t does not reach x. Its other exchanges are deletions.
All tested edges have tails at least w, so these operations cannot affect
the covers of e or ut. No new edge ends at or below x, so they do not
create a t-to-x path. Consequently e,f,r,g,ut retain the required covers
throughout this first preparation.

At its endpoint the only possible w-to-d path is the selected edge wd
itself. If wd is selected but xd is absent, transfer wd to xd using the
same two-covering-anchor construction. The arm wd now covers; the same
argument preserves e,g,ut. After this optional transfer there are two cases.

**No selected wd remains.** There is no w-to-d path. Exchange ut for tw
while retaining e. The new tw cannot bypass g, since w does not reach d.
The earlier incoming-arm theorem with the covers f,r,g,tw now replaces
tw by tx. This gives (18) for the prepared background.

**Both wd and xd remain selected.** The arm wd covers, but xd may still
be redundant. List increasingly all selected xy with x<y<d and y reaching
d. Exchange xy for yz while retaining r. The first-edge argument makes
each processed xy a cover; the sweep exposes xd. It preserves f too:
w cannot reach any such y<d, since every proper first edge of a w-to-d
path has already been removed. All added edges end at z>d, so g remains
a cover. The covers of e,ut,wd are unchanged. We can now use the proved
four-flip row

    xd -> tx [retain g],
    ut -> tw [retain e],
    tw -> wx [retain tx],
    wx -> xd [retain wd].                            (19)

It restores wd,xd and changes only ut to tx. The edge g may become
redundant at the endpoint; it is not retained in a later preparation flip.

Finally undo the x-sweep, if used, and then all w-arm transfers, in reverse
order. Every tested interval in those preparations starts at or above w.
The only endpoint changes are removal of ut and insertion of tx, whose
tails u,t are below w. Neither edge can occur in a forward path testing
one of those intervals. Thus every inverse flip remains actual, and all
background edges are restored. This proves (18).

The hypothesis includes the whole earlier one-sided class. If w does not
reach d, I is empty. If x does not reach d, selecting any xv with v in I
would contradict that condition. It also includes comparisons where both
roots reach d, and the case of a shared direct pair wd,xd even when those
arms initially have bypasses. The earlier four-flip theorem without cover
assumptions on f,r retains its separate broader scope on those anchors.

### The precise residual shared-branch configuration

The same preparation narrows the remaining obstruction under the initial
cover hypotheses. Suppose the proposition's condition fails, and let v be
the smallest member of I for which xv is selected. Transfer all earlier
proper w-arms reaching d from w to x, as above. The edge wv now covers.
Then clear alternative x-to-v paths by processing selected xy, x<y<v,
y reaching v, increasingly, with xy->yz [retain r].

This sweep preserves f: a w-to-y path with y<v would begin at an earlier
member of I, whose edge was removed. It preserves g,e,ut by the same
interval argument. We obtain

    wv and xv covering,       x<v<d,       v reaching d,

while e,f,r,g,ut still cover. The v-to-d reachability is unchanged: each
completed arm transfer changes only edges from w or x, and each x-sweep
addition ends at z>d. The preparation is actual at both comparison
endpoints, because their difference ut versus tx lies below every tested
tail. Any exact repair of this prepared pair therefore lifts back by its
inverse. The next section proves that repair.

Thus, with the initial anchors covering, we no longer need a separate
argument for arbitrary redundant proper arms: either the construction
finishes, or it reaches a shared pair of COVERING arms to a vertex v<d
which still reaches d. Other failures of the initial cover hypotheses,
and the full source-addition reducibility statement, remain open. The next
section supplies the missing shared-covering-branch repair and combines
the two cases into the covering-anchor corollary.

### Why the outer anchors cannot simply be omitted

The weaker claim using only e,g,ut and common reachability of w,x to d is
false. In area 012234, with strict corners 02,15, take

    A={01,02,15,24,35,45},
    B={02,13,15,24,35,45}.

Here (u,t,w,x,d)=(0,1,2,3,5). The edges e=02,g=15,ut=01 cover in A;
wx=23 and tx=13 are absent. Both w and x reach d, and t does not reach x.
Nevertheless A and B belong to different actual components.

Delete g from B. Its selected-edge envelope has maximal intervals
02,13,24,35. Every state in the resulting whole component retains 13,35,
so reinserting g makes it redundant through 1->3->5. An actual flip
cannot retain g; every other retained long and both its shorts stay in
that envelope. Thus the inserted family is closed under all source flips
and g is redundant throughout B's source component. The state A, where
g covers, lies outside it. This proves separation without using the
component-count diagnostic.

Adding vertex 6 and outer edges 26,36 gives the actual left DN configuration
with strict 02,15,26. It now satisfies the proposition: its only proper
w-arm reaching d is 24 and 34 is absent. The constructed path has eleven
flips. The counterexample therefore explains the role of the outer anchors;
it does not refute the left DN comparison with those anchors present.

### Verification

Related Rust: the external `first_join_tree_lifts.rs`, option
`--left-exclusive-cut`, reuses `two_anchor_path`, `incoming_anchor_path`
and the established cover/flip oracle. Three fixed states are checked:

| Natural area | Selected source edges | Completed path |
| --- | --- | ---: |
| 0122344 | 01,02,15,26,36,24,35,45 | 11 flips |
| 012234566 | 01,02,17,28,38,24,25,45,47,57,37 | 21 flips |
| 012234566 | 01,02,17,28,38,24,25,45,47,57,27,37,36,67 | 22 flips |

The last example starts with both wd=27 and xd=37 redundant. Its
preparation transfers two proper arms and then clears three x-arms;
the central repair is (19). Every actual flip, retained strict edge and
exact restored endpoint is checked. No seven- or nine-vertex state space
is enumerated. A separate fixed six-vertex probe finds the displayed
two-anchor obstruction (and one further failure) among 17 qualifying
states; the envelope argument above is its proof.
Receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/left-common-cone-20260929/`.
No Lean/Lake build, new reviewer, worker, consultant or maintained Rust edit
was used. This continuation does not claim unrestricted left reassembly.

## Closing the shared covering branch

The residual configuration just isolated admits a repair. We must delay
restoring xv until after restoring the borrowed v-to-d suffix. A second
outgoing cut removes the competing x-branches during that restoration.
This closes the preceding residual case with arbitrary exterior.

**Shared-branch lemma.** Suppose

    u<t<w<x<v<d<z,             x=w+1,

and A selects uw,ut,td,xz,wv,xv as covers. Suppose wx,tx are absent,
t does not reach x, and v reaches d. Then

    A ~ A-ut+tx.                                      (20)

Every other edge is restored. We do not require wz to cover, or even to
be selected. All reachability and cover tests use the full selected graph.
All new edges are contained in one of the selected natural intervals
uw,td,xz,wv, so they are natural; no removed edge is a natural corner.

### Borrowing tv

Write g=td and r=xz. Let H consist of the selected incoming edges hd
with v<=h<d and v reaching h in A. In decreasing order of h, exchange

    hd -> th [retain g].

Each hd is a cover at its turn: a bypass would end in a later incoming
edge kd with h<k<d, and that edge has already been removed. The same
argument says that h no longer reaches d after this exchange, so g stays
covering. The new th was absent, since g covered before the exchange.
The cut removes every v-to-d path. Its added edges start at t<x, so r,
wv,xv remain covering; uw,ut are unchanged as covers as well.

Let h be the smallest tail in H. The edge th now covers. Choose a path
of covers from v to h. This path survives the cut because its heads are
below d. Working backwards along it, exchange

    ab -> ta [retain tb].

At each step tb and ab cover. The new ta cannot already be present or
have a bypass: before the preparation t did not reach a, since a reached
d and g covered; the earlier added t-arms end to the right of a. Removing
ab prevents a new bypass of tb. This produces a covering tv and preserves
g,r,uw,ut,wv,xv as covers. Call the full borrowing path P.

The path P deletes only edges whose tails are at least v and whose heads
are at most d. It adds only edges ta, with v<=a<d and a reaching d in
the original A. These interval facts will justify its inverse after the
central exchanges.

### The central exchanges and the second cut

Apply the three actual flips

    xv -> tx [retain tv],
    ut -> tw [retain uw],
    tw -> wx [retain tx].                            (21)

The first is actual by the three displayed covers and t not reaching x.
For the second, no newly added edge can affect uw or ut. For the third,
tw covers because uw covered with ut present before that exchange, and
tx still covers after inserting tw: without wx, adjacent w cannot reach x.
At this point xv is absent and wx is selected. We have not restored xv.

Using ORIGINAL reachability in A, define

    J={a : x<a<=d, a!=v, xa selected in A, a reaches d in A}.

In increasing order, exchange xa->az while retaining r. These are actual
flips. The path P only deletes edges in the interval [x,d], and (21)
adds no edge starting at or above x. If xa has a bypass, its first edge
is an earlier xb leading to a and hence to d in A. It belongs to J and
has already been removed; the exceptional xv is absent. Thus xa covers.
The new az is absent because r covers. The exchange keeps r covering.
Edges ending at z>d do not create a new bypass of a later xa.

After this cut, x reaches none of the vertices a<=d that reached d in A.
Indeed, every such path would start in J or in xv, and all those first
edges have been removed. This remains true as we restore edges of A
inside [v,d].

### Restoring the background in the required order

First undo P. Each tested edge in its inverse is contained in [t,d].
Removing xv and the J-arms only destroys bypasses; the new az edges end
above d. The new tx cannot bypass a tested edge ta, because x reaches no
such a after the second cut. Nor can wx create a bypass: t did not reach
w in A (otherwise ut would bypass uw), and all newly added t-arms end
strictly above w. Every selected short and retained long used by the
inverse of P is still present, since none is an x-arm or wx. Every
inverse flip is therefore actual.

Now undo the J-cut, in decreasing order, retaining r. To verify this
without relying on the changed status of g, compare with

    A - xv - ut + tx + wx.

The edge r covers in this graph: both added edges start below x. The
forward J-cut is actual there by the same first-edge argument. After
undoing P we are exactly at its endpoint, so its inverse is actual.
Restoring these x-arms may make g redundant, but we no longer test g.

Finally exchange wx->xv while retaining wv. Originally xv covered, so
there is no x-to-v path after removing xv. Hence adding wx did not
bypass wv. The adjacent wx is a cover. This last flip is actual and
leaves exactly A-ut+tx. This proves (20).

If P has b flips and J has j edges, the construction has 2b+2j+4 flips.
For the one-edge suffix v->d with no competing x-arms it is the six-flip row

    vd -> tv [g],       xv -> tx [tv],
    ut -> tw [uw],      tw -> wx [tx],
    tv -> vd [g],       wx -> xv [wv].                (22)

The order matters: restoring xv before undoing P would make tv redundant
and invalidate the naive inverse.

### Consequence for the left DN comparison

Combine (20) with the preceding proper-arm preparation. We obtain:

**Covering-anchor left repair.** For u<t<w<x<d<z with x=w+1, suppose
uw,wz,xz,td,ut cover in A, wx,tx are absent, and t does not reach x.
Then A~A-ut+tx, with all exterior restored, without any further restriction
on w-to-d or x-to-d paths.

If every proper w-arm reaching d has its companion x-arm absent, use
(18). Otherwise the proved preparation exposes the first shared pair
wv,xv with v<d and v reaching d. Apply (20) and undo the preparation;
its flips are actual at both comparison endpoints by the earlier interval
argument. This settles all cases under these initial cover hypotheses,
including initially redundant direct arms wd,xd. The earlier direct
four-flip result has separate scope when wz,xz fail to cover.

The full left comparison still has cases where the initial anchors fail
to cover. The DD boundary with opposite invariant upper-corner status
requires the proved source-addition equations, not a path of this kind.
Independent reduction of all extra members of the homogeneous source
unions, and hence the requested general component recurrence, remains open.

### Checks of the shared-branch construction

Related Rust: external `first_join_tree_lifts.rs`, `left_shared_path`,
option `--left-shared-path`. Three fixed states check all actual flips,
strict-edge preservation and exact endpoints:

| Natural area | Incoming cut | Backward path | Competing x-arms | Total flips |
| --- | ---: | ---: | ---: | ---: |
| 0122344 | 1 | 0 | 0 | 6 |
| 0122345677 | 1 | 2 | 4 | 18 |
| 0122345677 | 3 | 0 | 4 | 18 |

The latter two have both a competing branch below v and redundant x-arms
above it, including xd. They separately exercise a borrowed suffix of
length three and an incoming cut with three edges. Exact edge lists and
the consumer snapshot are in the receipt directory already cited above.
The option `--left-shared-fork` also checks a three-flip normalization
at both endpoints of one fixed nine-vertex configuration. A bounded
search on the smallest seven-vertex example found (22), visiting 587
states; the proof and the longer fixed checks use the explicit construction.
No ten-vertex state space is enumerated. No Lean/Lake build or additional
worker was used, and no independent review is claimed.

### It suffices that one outer anchor covers

We can weaken the last corollary further. Keep uw,td,ut covering and
all its other hypotheses, but require only that wz,xz are selected and
AT LEAST ONE of them covers.

If r=xz covers and f=wz is redundant, list decreasingly every selected
hz, x<h<z, with w reaching h. Exchange hz->xh while retaining r.
Every bypass of the redundant f ends in this cut: the remaining possibility
of ending in xz would require w to reach x, excluded by adjacency and
the absence of wx. At each step hz covers by the last-edge argument;
the exchange keeps r covering. The cut leaves f covering as well. Its
new x-arms cannot create a path from w, which still cannot reach x.

If f covers and r is redundant, reverse the roles of w,x: for every
selected hz with x reaching h, exchange hz->wh, again in decreasing
order. Now f remains covering and r becomes covering. Since x>w, the
new w-arms cannot be reached from x.

Both preparations preserve uw,ut,td as covers. Their added arms start
at w or x; t reaches neither root (uw with ut excludes t-to-w, and
t-to-x is assumed absent). They add no edge ending at or below x, so
these nonreachability conditions persist. All their tested tails are at
least w. Thus the same preparation is actual at A and at A-ut+tx, and
its inverse lifts the covering-anchor repair back to the original pair.

**One-outer-anchor left repair.** Under the remaining hypotheses of the
covering-anchor corollary, one covering outer anchor is enough; the other
may be redundant. No bound on exterior size or cycle rank is needed.
The residual cover failures are therefore at uw,td,ut, or at BOTH outer
anchors, subject to whichever covers are already forced by the target
comparison. We do not assert that these failures occur independently.

The external option `--left-one-outer` checks both directions on fixed
area01223455 states. Each uses one incoming-cut flip, the six-flip shared
repair, and the inverse cut: eight flips with all exterior restored.
The composed nine-vertex normalization and shared repair also pass
`--left-shared-fork`, with twelve flips. These are fixed path checks,
not an enumeration of either state space.

## Covers at the other endpoint of a left comparison

2026-09-29 continuation. The preceding repair was stated with covers at
the ut endpoint. We now allow the covers to occur at the tx endpoint.
This is useful because the corner-difference reduction supplies witnesses
with all strict corners covering, without prescribing the endpoint.

Let A,B be the two source preimages of an actual left R10 flip:

    u<t<w<x<d<z,       x=w+1,
    A=Q+uw+wz+xz+ut,   B=Q+uw+wz+xz+tx,

with wx absent and a selected g=td. The actual target flip retaining ux
implies that ut covers in A, tx covers in B, and t does not reach x
in A. Changes between target and source cannot affect these intervals:
the new f=wz ends above x, while the removed ux starts below t.

**Reverse-endpoint lemma.** Suppose uw and g cover in B, and at least
one of wz,xz covers in B. Then A and B are connected by actual source
flips, restoring all other edges. We impose no cycle-rank bound or
condition on exterior paths.

Since tx is selected and g covers in B, x does not reach d. This is the
additional nonreachability that lets us prepare both endpoints.

First arrange that r=xz covers. If it already covers, do nothing. Otherwise
f=wz covers. In decreasing order, replace hz by wh while retaining f,
for every selected hz with x<h<z and x reaching h. The usual incoming
cut exposes r and preserves f. It also preserves g in B, even though
t may reach w: every new head h was reachable from x and therefore
did not reach d. These h-to-d paths cannot be created by the preparation,
whose added edges start at w<h. Thus no new path through wh bypasses g.
The cover of uw is unchanged, since every added head lies above x>w.
All tested intervals start at w or later, so this preparation is actual
at both A and B. It preserves their difference ut versus tx.

Now clear the t-to-w paths. In the prepared B, list increasingly every
selected th with t<h<=w and h reaching w. Exchange

    th -> hd [retain g].                            (23)

Each th covers at its turn, by the first-edge argument. Its companion
hd is absent since g covers. The flips preserve g and eliminate every
t-to-w path. The case h=w, which can insert wd and make f redundant,
is INCLUDED. This is why we exposed r first: all newly inserted edges
start at or below w<x, so they do not affect r or the fact that x does
not reach d. We need only r covering after this sweep.

The same sweep is actual at A. The edge ut starts below every tested
tail, and the extra tx in B cannot affect a th cover since h<=w<x.
It cannot affect g either, because x still does not reach d. The cover
of uw in B persists: all added hd end above w. Call the endpoints
A*,B*. The state A* now has uw covering as well. Its only additional
edge relative to B* is ut; a new bypass of uw using ut would require
the t-to-w path we have just removed. The original ut remains a cover,
as all preparations occur above its head t.

Thus A* satisfies the proved one-outer-anchor left repair: uw,td,ut,r
cover, wx,tx are absent, and t does not reach x. It follows that
A*~B*. Undo (23) and then the initial incoming cut along their recorded
actual paths at B. This gives A~B and restores every other edge.
In particular, we do not try to retain the possibly redundant f in
the middle stage. This proves the reverse-endpoint lemma.

**Either-endpoint corollary.** For an actual left comparison as above,
it suffices that uw,td and at least one of wz,xz cover at EITHER source
endpoint. The short-edge cover conditions are supplied by the actual
target flip. The forward endpoint uses the preceding theorem; the reverse
endpoint uses (23).

### Verification of the reverse preparation

Related Rust: external `first_join_tree_lifts.rs`, option
`--left-reverse-covers`. Two fixed states start with uw redundant in A,
while uw,td,wz cover in B. The area0122344 example uses eight flips.
The area01223445 example also starts with r redundant and uses ten flips,
including the preliminary incoming cut. In both, the t-to-w sweep inserts
wd and makes f redundant, so a proof requiring both outer anchors to remain
covering at that point would fail. The diagnostic checks each actual flip,
strict-edge preservation and the exact restored endpoint.

One fixed six-vertex source, area012233, has sixteen actual left R10
comparisons. Six have uw,td,wz covering at A; two additional comparisons
have those covers only at B. These eight pairs lie in the same actual
source component, as proved. Of all sixteen comparisons, only one pairs
different source components, and both its endpoints fail the three-cover
condition. These finite counts are not used as the uniform proof.
Sources and receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/left-endpoint-covers-20260929/`.
No maintained Rust or Lean source changed; no Lean/Lake build, worker,
consultant or independent review was used.
