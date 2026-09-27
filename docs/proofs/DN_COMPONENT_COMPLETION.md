# Completing components before the ordinary DN recurrence

Status: the transport and conditional induction below are proved in prose.
The active-component isolation assertion is **open**. This note makes the
author's proposed redistribution precise for one ordinary recurrence; it
does not prove the full component theorem or the primitive circular case.

The [recurrence note](FLIP_COMPONENT_INDUCTION.md) owns the local semantic
identities, endpoint flip maps, corner reductions and general integer
transport criterion. We use K for strict coloring enumerators and E for
evaluated HRV elementary monomials, with the same finite alphabet.

## Setup and the correction allowed by induction

Use a saturated ordinary eligible DN instance, with vertices u<w<x<z,
x=w+1, strict source corners e=uw and f=wz, and source normal pairs
q=wx, r=xz. The target has strict ux,xz and local normal pairs p=uw,q=wx.
All other strict edges remain fixed. We retain the full hypotheses of
`Diagram.dnSuccessor`: contact, equal adjacent areas, the length bound,
no strict head at x, and the terminal strict gap. Ordinary means that every
natural edge is increasing in this linear vertex order. Saturated means
every natural corner is strict.

Write L_ab(Q) for a source state with local bits (q,r), and R_ab(Q) for a
target state with local bits (p,q). Q ranges over subsets of the common
exterior normal pairs. The adjacent transposition of w,x induces an
involution σ on these subsets. Every such state is acyclic in this ordinary
setting. Brackets [A] below denote the ENTIRE source flip component of A.

Call a source component f-active if f is a cover in at least one of its
states. An f-inactive component has f redundant in EVERY state, so the
proved strict-corner deletion lemma identifies it with an entire component
of the smaller diagram L\f, preserving both valuations. A redundant state
inside an active component does not justify that reduction.

For an active component C, we seek a union consisting of C and some complete
f-inactive components. We transport the union through DN and then subtract
the already-solved inactive components. This allows individual orientation
occurrences to be redistributed without claiming a component bijection.

## Two cover-preserving lifts

Every exterior source flip in the 00 stratum also occurs in the 01 stratum,
with the same exterior endpoints. Indeed, adding r can alter the cover test
of another natural edge only if that edge properly contains the interval r.
The terminal gap implies that f is the only such edge. An alternate w→z
path using the added r would first need a w→x path. Since x=w+1 and q is
absent, there is no such path. Thus even f's cover test is unchanged.
The exchanged exterior shorts and retained long survive, their cover tests
on both sides agree, and ordinary acyclicity is automatic.

Dually, every exterior target flip in the 00 stratum also occurs in the
10 stratum, by adding p. The only target natural edge properly containing p
is ux: p was a source corner and ux is the sole added natural pair. A new
alternate u→x path using p would need w→x, again impossible without q.
Thus all required cover tests agree. These are inclusions of flip graphs;
the larger stratum can have extra flips retaining the newly selected edge.

We also obtain a useful path lift: every exterior source 10 flip lifts to
source 01. Delete q first. It is adjacent, so cannot be the retained long,
and exterior flips do not exchange it. Deleting it preserves the cover
tests required by the given flip. Then apply the source 00-to-01 lift.
This does not by itself connect the two middle states across a path that
leaves the 10 stratum.

### Preconditioning a crossing-corner flip

There is also a proved boundary step which applies beyond the adjacent
DN window. Let f=wz be a strict corner covering in an ordinary state A.
Suppose a crossing strict corner g=ab supports the actual flip aw→wb,
where a<w<b<z. If bz is absent, we can first perform f-long flips so that
this g-flip can be executed with f remaining a cover throughout the path.

For the proof, let I be the whole selected relation internal to (w,z), and
let L,R be the attachment sets: y∈L when wy is selected, and y∈R when yz
is selected. Covering of f is equivalent to L∩R=∅ and absence of any I-path
from L to R. Indeed, every alternate w→z path starts in L, stays internal
until its last edge, and exits through R. Strict edges are included in this
selected relation.

Consider the right attachments reachable from b in I. Because bz is absent,
all of them are strictly greater than b. Pick a reachability-maximal one y.
It reaches no remaining right attachment, so yz is a cover. The reverse
f-long flip yz→wy is valid and leaves f a cover: an earlier left attachment
could not reach y, and y reaches none of the remaining right attachments.
Both shorts are normal, being proper subintervals of the strict corner f.
Iterate; the finite number of right attachments reachable from b decreases,
and I remains fixed.

All changed edges end or start beyond b. They therefore cannot affect any
positive path testing the covers aw or ab, and they do not change wb.
The original g-flip is still actual. After performing it, a newly created
alternate w→z path would have to start with wb and then reach a remaining
right attachment from b. The preceding sweep excluded exactly those paths.
This proves the asserted path through f-cover states.

The exception bz selected matters. Then the sweep would insert wb before
the crossing flip; executing the latter instead creates both attachments
wb,bz and makes f redundant. Such a state may still belong to a component
active at both f and g, since it can be reached by an actual flip from a
state where both are covers. It cannot be discarded as a solved component
from this local configuration alone.

A useful directional observation accompanies the sweep. An actual rightward
f-long push wy→yz cannot destroy the cover status of a strict corner
crossing f from the left: its added edge ends beyond that corner. A corner
crossing f from the right cannot gain cover status: its deleted edge starts
before that corner. Nonoverlapping corners are unaffected; corners sharing
only an endpoint are unaffected for the same path-containment reason.
Thus normalizing an already-covering rightmost strict corner preserves all
other corners currently covering. This does not supply simultaneous cover
witnesses for a component active at every corner.

Astra supplied the crossing sweep; primary and Terra independently audited
the full cover tests, normality and finite termination. These are prose
lemmas, not Lean declarations or a completed component-isolation argument.

## A finite graph specifying every completion equation

Define a graph J whose vertices are entire source components. Add the
following undirected edges, allowing repetitions and loops:

| Trigger | Components joined in J |
| --- | --- |
| Every exterior subset Q | [L_10(Q)], [L_01(Q)] |
| Every actual target flip between middle states with exteriors Q,P | [L_01(Q)], [L_01(P)] |
| Every actual target flip R_00(Q) ↔ R_01(P) | [L_00(σQ)], [L_01(P)] |
| The same 00-to-01 flip | [L_01(σQ)], [L_01(Q)] |
| Every actual target flip R_11(Q) ↔ R_10(P) | [L_11(Q)], [L_01(P)] |

The known near-corner geometry makes this mixed-flip list exhaustive: target
p can toggle only against q, so the mixed types are precisely 00↔01 and
11↔10. Edges entirely within 00 or 11 require no additional generators.

Every J edge preserves the source normal ascent count. For the lower mixed
flip, |Q|=|P|+1, so L_00(σQ) and L_01(P) have equal counts; its second pair
also has equal counts. For the upper mixed flip, |P|=|Q|+1. The other rows
preserve cardinality directly. Therefore each J-connected class is a union
of source components at one ascent count.

**Reconstruction lemma.** Let h be any integer multiplicity constant on each
J-connected class. Regard it as a source orientation function and put
α(Q)=h_01(Q). Then h_10=α, and the multiplicities

    g_00(Q) = h_00(σQ) + α(σQ) − α(Q),
    g_10(Q) = g_01(Q) = α(Q),
    g_11(Q) = h_11(Q)

are constant on every entire target component. Furthermore,

    K_L(h)=K_R(g),                E_L(h)=E_R(g).

The semantic identities are the already-proved paired DN transport with
β=α. For reconstruction, check every actual target flip:

1. Middle-to-middle constancy is the second J row. A lower mixed flip uses
   the third and fourth rows, cancelling α(σQ)−α(Q) and identifying the
   remaining h_00(σQ) with α(P). An upper mixed flip uses the fifth row.
2. A target 11 flip corresponds to a source 11 flip with unchanged Q, by
   the proved full-stratum flip isomorphism. Thus h_11 is constant there.
3. A target 00 flip Q↔P corresponds to the source 00 flip σQ↔σP by the
   proved zero-stratum conjugacy. Source component constancy gives equality
   of h_00 at these exteriors. The source lift above gives
   α(σQ)=α(σP). Separately, the target lift gives a target 10 flip Q↔P;
   its middle-row generator gives α(Q)=α(P). All three terms of g_00 agree.

This proves reconstruction over the integers; negative target multiplicities
are allowed. In particular, no closed-walk consistency problem remains once
h is constant on the explicitly defined graph J.

## The remaining companion lemma and its precise consequence

The outstanding assertion is local to this recurrence, not the auxiliary
global AU_prime proposal:

> **DN completion isolation.** Every connected class of J contains at most
> one f-active source component.

Assuming it, take the J-class containing any f-active C, and let h be the
indicator of its union. Every other source component I in that class is
f-inactive. The reconstruction lemma gives, for X=K,E,

    X_C = X_R(g) − Σ_(I in the class, I≠C) X_I.

The right side is an integer combination of entire target components and
entire components obtained by deleting f. Thus their known component
identities imply K_C=E_C. Inactive C are already handled by deletion.
This proves the conditional DN component recurrence for every finite
alphabet, without a pointwise coloring-to-HRV identification.

The ordinary induction measure is explicit. If a_j are the area entries,
use lexicographic order on

    (doubledArea, M),       M=Σ_j j a_j.

DN increases a_x by one and decreases a_z by one, leaving the strict count
unchanged. Doubled area is therefore unchanged, while M_R+z=M_L+x;
x<z gives M_R<M_L. Deleting strict f decreases doubled area by one.
This justifies both kinds of smaller diagram in this conditional step.
It does not supply the other recurrence transports, and this linear moment
is not asserted to decrease across a wrapping circular DN move.

The isolation assertion is sufficient, and may be stronger than necessary:
it uses 0/1 source corrections at one ascent and fixes β=α. A failure would
leave the more general signed target/deletion transport available. It would
not refute the component formula or the author's recurrence approach.

The user's minimum-area induction is formulated in the
[general recurrence note](FLIP_COMPONENT_INDUCTION.md#signed-recurrence-generation-without-a-uniqueness-requirement).
It allows deletion at ANY inactive strict corner and signed combinations of
several packet equations. The general target is spanning the unsolved
component classes by certified recurrence rows, rather than requiring the
particular J-grouping to isolate each class by itself.

## Why the inactive additions are necessary

One exact obstruction to leaving the deletion residual unchanged occurs in
the saturated ordinary diagram with zero-based areas (0,1,1,2,3,4), strict
{01,15}. Take Q={13,23,24,45}, q=12 and r=25. L_10(Q) belongs to the
complete inactive component I with the following normal selected sets:

    {12,13,23,24,45},
    {12,13,24,34,45},
    {13,23,24,34,45}.

Its successive flips are 234 and 123; f=15 is redundant throughout.
L_01(Q) belongs to a different, f-active component C of size 84. For h=χ_C,
δ(Q)=h_10(Q)−h_01(Q)=−1. In L\f there is an actual reverse 123 flip

    del00(Q) ↔ del10(Q\{23}),

retaining 13. The canonical residual
Σ δ(P)([del00(P)]−[del01(P)]) has coefficient −1 at the first endpoint and
zero at the second. Thus even its r-absent sector is not component-constant.
Replacing h by χ_C+χ_I makes this particular δ(Q) zero. This repairs the
displayed boundary, not automatically every boundary of the diagram.

Primary checked the complete components with both the existing model and
the Rust component binary. The test above does not use a truncated component.

## Bounded evidence and the unresolved proof

The full J construction was checked on fixed saturated ordinary fixtures:

| Areas | Strict pairs | Source components | J classes | Classes with two f-active components | Nonconstant target images |
| --- | --- | ---: | ---: | ---: | ---: |
| (0,1,1,2,3,4) | {01,15} | 116 | 71 | 0 | 0 |
| (0,1,2,2,3,3) | {02,14,25} | 26 | 19 | 0 | 0 |
| (0,1,2,3,3,4,4,4) | {03,15,26,37} | 1395 | 654 | 0 | Not recomputed |

These exact checks test every J-class indicator and every target component
in the first two fixtures. The third tests isolation on the entire source
state space for a local shape with two crossing strict corners at the chosen
DN window: e=03, f=37, x=4, with crossing corners 15 and 26.
It has 131072 source states and 76 f-active components. All five types of
J-generators were included. This was one fixed geometry, not a scan over
area sequences; the already-proved target reconstruction was not recomputed.
These are evidence for isolation, not its proof. Joining
only the source middle pairs is insufficient for target reconstruction in
both fixtures; the target-generated joins in J are necessary to the present
construction.

A possible proof direction is to follow actual paths until f becomes a
cover and lift their exterior portions. The proved 10-to-01 lift handles a
path remaining in that stratum. A path can instead remove q, enter a 00
region where f remains redundant, and expose f only later. That excursion
is not resolved. Statewise redundancy along it does not certify whole
inactive components. Contracting f (after removing f itself) makes a directed
cycle exactly when f was redundant, but gives no uniqueness theorem by
itself. The enlarged moves can also exchange a redundant short; describing
them as relaxing only the cover test on the retained f is incorrect.

A further test on this SAME third diagram rules out one shortcut in the
description of J. Allowing every short exchange wy↔yz around f, regardless
of covers, gives 315 classes and no f-active collision, but does NOT contain
all the J-generators. Some middle and lower mixed rows join different such
classes. Hence a theorem just about relaxed f-long exchanges would still
need an additional DN transport argument. No general conclusion is drawn
from its finite no-collision result.

Primary formulated the graph and checked the two fixtures. Terra audited
the reconstruction and ordinary measure; Astra audited the structural
obstructions. No Lean theorem is claimed for these new results.

Receipts are under the external requests directory `component-recurrence/`:

- `completion_graph_probe.py`, SHA-256
  `45593f7e25843112c866d9e4cd858fd51e427d4380f7fea6a40c8b6f05865cd9`;
- `completion_graph_fixed_fixtures.json`, SHA-256
  `01826e5f7a48d36b2e6d7ddf92ce6f4461f23722664bbb2a51e173bf94008abb`;
- `r_absent_boundary_certificate.json`, SHA-256
  `267c589f7b8fa83ad20ef56c4b3055c6a0112798527f35049bf4cab3c17b9625`;
- `two_crossing_completion.py`, SHA-256
  `8d32abfefea1b365889fbe84ca7f90e23af7cf6a3ac62f49bb672b5cd887d698`;
- `two_crossing_completion_result.json`, SHA-256
  `c6dcbf7cc95518ab07b7bd2e7e05146292bbc5f7825db151d4a7b6f6adf107a7`;
- `relaxed_contains_completion_result.json`, SHA-256
  `af84837102ddd5f14ac0390de4fc17aafbc29cbe0e612cd6bc5861c87b409b2d`.

The bounded Python orchestration reuses the previously audited `probe.model`;
it introduces no new enumeration engine or polynomial generator. The Rust
cross-check uses `component_source_probe` with complete-component caps 500
and seeds 1143,1269 on the first fixture. Its masks are over all natural
edges, whereas `probe.model` uses normal-edge masks. No source build was run.

For the larger fixed diagram, primary reused the returned ordinary
`dnmodel.py` (saved as `returned_dnmodel.py`, SHA-256
`d92d453ab7e3779f375055ba8ecaa2e9b35d28ee2d2a7448f75ba8fb7d40f171`).
Primary audited its forward reachability and actual flip enumeration, then
checked exact equality of its entire-component partitions with `probe.model`
on BOTH preceding fixtures before use. Its component BFS avoids the earlier
model's quadratic diamond-row deduplication. The Rust capability check was
refreshed; this one-off equivalence comparison introduced no new graph engine,
shared library code or polynomial generator. Native bounded jobs are terminal.
