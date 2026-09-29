# Middle-state transfer at an exposing flip

2026-09-29. We prove a uniform actual-flip construction for the ordinary
diagram recurrence. It removes the unicyclic hypothesis from both the
left and right local exposure lemmas. The construction retains arbitrary
exterior and restores every edge other than the two middle shorts.
It does not yet transport a middle state through an arbitrary path that
leaves and later re-enters the selected-short sector.

## A general exposing-exit lemma

Let a<b<c be vertices in an ordinary natural diagram, and write

    f=ac,       q=ab,       r=bc.

Let A select f,q and omit r, with f redundant. Suppose an actual flip
removes q and gives a state B in which f covers. Then

    A ~ A-q+r,                                          (1)

where ~ denotes membership in the same complete actual-flip component.
We do not require connectedness, a cycle-rank bound, or adjacency of a,b.
The edge f need not be a natural corner or strict.

The exposing flip has exactly one of the following forms:

| Side | Removed edge | New edge s | Retained long h |
| --- | --- | --- | --- |
| left | ab | ta | tb, with t<a |
| right | ab | bd | ad, with b<d and d!=c |

The case d=c would retain f, impossible since f is redundant in A.
If f is a natural corner, the right case necessarily has d<c; we do
not need that extra bound. All the strict decorations are retained.

Put P=A-q. Then B=P+s, f covers in P, and P has no a-to-b path:
the latter follows because q was a cover in the actual exposing flip.
In the right case P has no b-to-d path either, since such a path,
preceded by q, would bypass the covering long ad in A.

### The incoming cut

We use the following finite list, determined by P alone:

    I={v : b<v<c, vc is selected in P, b reaches v in P}.

Starting at B, process I in decreasing vertex order, using

    vc -> av [retain f].                              (2)

Every exchange is actual. To see this, suppose we are processing v.
A bypass of vc would end in uc with u>v. A path starting at v cannot
use the new edge s: its tail is below v in both cases. Nor can it use
any newly added edge ay, whose tail is a<v. Every path below c is
therefore an original path in P. Hence b reaches u in P, so uc was
already removed at the earlier stage u. This contradiction proves that
vc covers. The edge f is a cover initially and remains a cover under
each actual f-retained flip. Its cover also ensures that av is absent.

Write P* for P with these incoming edges replaced by their av partners.
The prepared state is B*=P*+s. There is no b-to-c path in P*: every
original such path ends in an edge vc with v in I (the direct edge
r was absent), and all those edges have been removed. New edges start
at a<b, so they create no new path starting at b.

### Reinsert q, then change the middle state

At B* we can undo the original exposing flip, replacing s by q and
retaining h. Here "short" refers to its role in the triangle; a,b need
not be consecutive labels.

In the left case, neither added av can affect a cover test ending at
a or b, since v>b. Thus both s=ta and h=tb still cover. In the right
case, new edges starting at a cannot bypass s=bd. A new bypass of h=ad
would start with some new av and continue from v to d in P. Since
b reaches v in P, this contradicts the absence of a b-to-d path.
Deletion of incoming edges cannot create a bypass. This proves both
cover tests for the inverse exposing flip, in either case.

We have reached P*+q. The edge q covers: its original cover in A has
not changed inside [a,b]. The edge f also covers. It covered in B*,
and the newly inserted q cannot give a bypass because P* has no
b-to-c path. We can therefore perform

    q -> r [retain f].                               (3)

### Restore the full exterior

We undo (2) in reverse order. At corresponding stages, the reverse
state differs from the original forward state by removing s and adding r.
Removing s cannot spoil any cover. Adding r cannot affect a tested av,
whose head is below c, or a tested vc, whose tail is above b. It cannot
bypass f either: there is still no a-to-b path. This path was absent
in P, and all preparation edges have heads above b.

All reverse flips are therefore actual. They restore P exactly and
leave the endpoint P+r=A-q+r. Counting the initial exposing flip,
the |I| preparatory flips, its inverse, (3), and the |I| restoring flips,
the construction has 2|I|+3 moves. This proves (1).

The two edges exchanged in every preparation lie properly inside the
natural edge f. They cannot be strict corners, so all preparations are
allowed in the decorated diagram. The original exposing flip and its
inverse were allowed by hypothesis. This proves the assertion with
all other strict edges and all exterior arrows present.

Reflecting the vertex order and reversing every forward edge proves the
dual statement: if A selects f,r, omits q, and an actual r-removing flip
makes redundant f cover, then A~A-r+q. Reflection is used only for the
actual flip graph, not as an asserted HRV-valuation identity.

## Consequence for NN and DN middle coefficients

In the eligible NN notation, take f=ac, q=ab, r=bc, b=a+1. In the
eligible DN notation take (a,b,c)=(w,x,z), with the additional strict
edge uw and all common exterior unchanged. The only natural edge
properly containing r is f in these geometries.

For a complete source component C let h be its indicator and put

    delta(A)=h(A)-h(A-q+r)       for q selected, r absent.

If f covers in A, its own triangle already gives delta(A)=0. The
lemma proves the same equality whenever a q-removing flip exposes f,
with no unicyclic restriction. It replaces the corresponding local
left/right exposure arguments in
[inactive NN corrections](COMPONENT_NN_INACTIVE_CORRECTIONS.md) and
[the leftward transition](COMPONENT_LEFT_EXIT.md).

There is a slightly stronger useful conclusion. If A has ANY actual
neighbor in which f covers, then delta(A)=0. When that flip preserves
q,r, delete the preserved q and insert r at both endpoints. Deleting
q cannot remove a retained long, since q is adjacent, and all remaining
tested covers survive. Inserting r can affect only f. The original
flip cannot retain f while f is redundant, so it lifts to the middle
images. At the exposed endpoint q->r is actual. If instead the flip
removes q, apply the lemma. It cannot insert r while preserving q,
since the resulting q,r would make f redundant. These exhaust the cases.

More generally, suppose a path starts at A, keeps q selected and r
absent until its final step, and ends where f covers. We truncate it
at its first exposure of f. The q-preserving
lifts and the last-step lemma give A~A-q+r. Thus a nonzero unmatched
middle coefficient must avoid every exposure reachable in this way.

This identifies the remaining obstruction precisely. On a path from
a nonzero middle state to an f-covering state, q must first disappear
while f is STILL redundant, and subsequent q-free states must be
controlled before applying this argument. The cut construction does
not prove that such a detour can always be replaced by a q-preserving
path. Nor does it prove the general left retained-e-prime repair or
the simultaneous collection into whole target components.

## Bounded exact verification

Related Rust: the existing external `first_join_tree_lifts.rs` consumer,
option `--general-exposure-check`, reuses
`component_source_probe::{cover,flip}`. The consumer constructs precisely
the stated cut path and verifies every actual flip, preservation of
strict edges, and the exact final edge set. It does not infer a path
from equality of polynomial valuations or from component enumeration.

| Natural area | (a,b,c) | Left exposing flips | Right exposing flips | Constructed flips checked |
| --- | --- | ---: | ---: | ---: |
| (0,1,2,3,4,5) | (0,1,5) | 0 | 93 | 483 |
| (0,1,2,3,4,5) | (0,2,5) | 0 | 34 | 170 |
| (0,1,2,3,4,3,4) | (2,3,6) | 546 | 128 | 3526 |

These are all applicable exposing flips in three fixed positions, not
a scan over diagram families. An additional fixed state checks normal
f=03 and exposing long 04, beyond the end of f. Another fixed state
on ten vertices has six simultaneous bypasses 0->1->v->9, for
3<=v<=8, with retained exposing long 02. Its six-edge incoming cut
gives fifteen actual flips. No ten-vertex state space is enumerated.

Frozen sources, before-files and logs are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/corner-exposure-20260929/`.
The proof above treats arbitrary exterior; finite checks are supporting
verification. No new independent reviewer, Lean/Lake build, or manuscript
build was used, and maintained Rust sources are unchanged.
