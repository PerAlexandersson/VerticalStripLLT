# Moving an incoming edge with a selected containing interval

2026-09-28. We prove an incoming-edge transfer, including edges on the
unique cycle, when a suitable containing interval is already selected.
Primary and Astra independently audited the case split and cover tests.
The more general saturated NN case with a containing corner uv, u<t,
remains open when tv is not selected.

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
