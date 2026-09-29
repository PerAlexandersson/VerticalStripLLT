# Choosing a forward recurrence at the first area drop

2026-09-29. We prove recurrence coverage for every ordinary saturated
diagram. Together with the already-proved DD/ND unmarking step, this closes
the choice-of-recurrence and induction-order obligations in the
[component outline](COMPONENT_RECURRENCE_OUTLINE.md). General NN/DN
reassembly into whole components is still unproved. We do not use the
separate completed component theorem.

## Ordinary coordinates and corner rows

On vertices 0,...,n-1 write a_j for the area and b_j=j-a_j. Thus

    a_0=0,  0<=a_j<=j,  a_(j+1)<=a_j+1,
    ij is natural exactly when b_j<=i<j.

The boundary b_j is nondecreasing. Set a_n=0 for the terminal comparison.
The natural corner ending at j exists precisely when

    a_j>0 and a_(j+1)<=a_j;

it is the edge b_j j. In a saturated diagram all these corners are strict.
We refer to a row as D if its incoming corner is strict, and N otherwise.
There is no incoming edge at row 0, which is N.

A natural diagram is connected precisely when a_j>0 for every j>=1.
If all these inequalities hold, all adjacent edges are present. If a_j=0,
then b_j=j and monotonicity excludes every natural edge crossing the cut
between j-1 and j. Thus natural connected components are consecutive
intervals, separated by zero area entries.

## The first-drop lemma

**Proposition.** Let D be a connected saturated ordinary natural diagram
with at least one edge of length at least two. Let t be the first index
such that

    a_(t+1)<a_t,

using a_n=0 at the endpoint. Put x=b_t and y=x+1. Then f=xt is a strict
corner of length at least two, with the required terminal gap, and its
contact at x,y is an eligible NN, ND, DN or DD contact.

**Proof.** Such a t exists because the area is positive after its initial
zero and the appended final entry is zero. The entries through a_t are
nondecreasing. If a_t were 1, connectedness would force t=n-1, and all
preceding entries would be at most 1. That would make every edge adjacent,
contrary to the hypothesis. Hence a_t>=2 and

    0<=x<y<t<n.

The strict drop makes f a natural corner, hence strict by saturation.
It supplies exactly the root-gap inequality a_(t+1)<a_t, including when
t=n-1. Since y<=t and t is the first drop,

    a_x<=a_y<=a_x+1.                                  (1)

There are only two cases.

If a_y=a_x+1, then b_y=b_x. Row x has no natural corner and is N.
According as row y is N or D, this is NN or ND. In the ND case write
g=b_y y. We also have a_x>=1: if a_x=0, then b_y=x and g=xy would lie
properly inside f=xt, contradicting that g is a natural corner. Thus all
the additional ND area-positivity and distinct-head requirements hold.

If a_y=a_x, then a_x>0, since xy is natural and a_y>=1. The incoming
corner e=ux, where u=b_x, is strict, and

    u<x<y<t,  b_y=u+1.

Row x is D. According as row y is N or D, this is DN or DD. In the DD
case its incoming strict corner is g=(u+1)y. The local area bound also
holds: a_x+1<=x+1=y<t<n. The heads x,y,t are distinct, so the strict
edges required in these cases are distinct as well.

These are the full ordinary local geometries: root length at least two,
strict root gap, the required boundary equality or area equality, and
the indicated strict/nonstrict contact rows. We impose no additional
condition on later entries beyond the chosen root gap, and none on the
selected exterior relation. This proves the proposition.

In particular, we need neither reversal nor a claim that the leftmost
strict corner is eligible. We choose the FIRST STRICT DROP in the area,
which can occur after a plateau of earlier strict corners.

There is an equivalent description directly in the corner diagram. Before
t, the boundary increments are zero or one. Starting from b_0=b_1=0,
each increment from i to i+1 supplies the corner with tail i. Thus the
strict corners ending before t have tails exactly 0,...,x-1, one each;
f is the next corner, with tail x. The drop gives b_(t+1)>=x+2, so no
strict corner anywhere has tail y=x+1. After unmarking its incoming
corner when necessary, y is incident to no strict edge. This identifies
the local diagrams used below without introducing another recurrence.

## Only NN and forward DN reassembly are needed

At this first-drop contact, use the following rule.

| Contact in D | Intermediate N | Apply at the same root f |
| --- | --- | --- |
| NN | D itself | NN |
| ND | Unmark the incoming corner g at y | NN |
| DN | D itself | Forward DN |
| DD | Unmark the incoming corner g at y | Forward DN |

If we unmark g, a component C of D remains exactly one whole component
of N. A maximal natural edge cannot be exchanged as a short, so its
selected status is constant on each component; the selected-g sector of
N has precisely the same states and actual flips as D. This is the
[one-component inheritance](COMPONENT_DD_PACKETS.md#direct-one-component-inheritance-for-dd-and-nd),
not an appeal to the unknown identity for N.

Write A=sum_j a_j and M=sum_j j*a_j. The intermediate N has the same
(n,A,M) as D. For NN the initial split lies in N-f, so A decreases by one.
For forward DN the target replaces the natural edge xt by uy. Therefore

    a_y -> a_y+1,  a_t -> a_t-1,
    A_target=A,   M_target=M-(t-y)<M.                 (2)

Its common deletion diagram has A-1 natural edges. Any source additions
must still be reduced independently to smaller whole components, as
required by the reassembly statement. Marking output corners changes
neither A nor M; deleting unused corners reduces A. Thus normalization
does not spoil any of these decreases.

The conclusion is stronger than merely listing eligible aggregate
recurrences. It specifies a move for ONE component, identifies the
equal-measure intermediate with that SAME whole component, and fixes a
forward direction whose final targets decrease the ordinary order.
What remains open is the collection of the exact NN/DN split into those
whole targets. We do not infer this from the area calculation.

For proving the full theorem, it suffices to establish that collection
at first-drop contacts. The source can be taken saturated, or with only
the corner g at y unmarked and C lying in its selected sector. An NN/DN
theorem with arbitrary exterior corner decorations would imply this,
but that stronger generality is not an additional induction requirement.

## Conditional completion of the ordinary proof

**Theorem.** Suppose the required NN and forward DN push-through identities
are proved at the contacts just specified, with the same integer
coefficients for K and E and whole output components strictly smaller
in (n,A,M). Then every ordinary component satisfies K(C)=E(C), and hence
has the claimed elementary expansion and shifted elementary positivity.

We give the induction to make the remaining dependency exact. Use strong
induction on the nonnegative lexicographic triple (n,A,M). Normalize C
to its saturated selected-edge envelope, preserving its whole flip graph
and both valuations. If normalization deletes an edge, A decreases and
induction already applies. If it only marks selected corners, it is a
representation change at the same measure; it invokes no induction
hypothesis. Denote the resulting saturated diagram by H.

If H has two or more natural connected components, its flip graph is
the Cartesian product of their flip graphs. Every triangle and every
directed cover test lies entirely in one natural connected component.
Consequently C is the full product of its projected components. Coloring
enumerators multiply over these disjoint vertex sets; HRV fiber partitions
concatenate, so the elementary expressions multiply too. Each factor
has fewer vertices, and induction gives the identity for C. The empty
diagram has K=E=1.

We may therefore assume H is connected. If every edge is adjacent,
all natural edges are maximal and strict. There is exactly one state,
the increasing chain; both valuations are e_n. Otherwise the first-drop
lemma supplies one of the four contacts. The table reduces it to NN or
forward DN without changing C. Apply the assumed push-through identity
and induction to every final whole component. The same signed coefficients
give K(C)-E(C)=0. This proves the theorem.

Finally E(C) is the original sum of elementary monomials, with coefficient
one for each selected state. Positivity follows from that sum, regardless
of signs in the recurrence. Every state of C has the same number k of
selected normal edges, so restoring the shifted weight multiplies the
identity by t^k. We never divide by the shift parameter.

Thus recurrence coverage, base cases, normalization and well-foundedness
no longer remain separate open assertions. The general NN/DN
whole-component push-through step remains the mathematical gap.

## Source correspondence and bounded checks

Related Lean (read only; no declarations added or builds run):

- `VerticalStripLLT/Circular/FirstBounceRecurrences.lean`,
  `Diagram.coloringLLT_shortenStrict_NN`: root length/gap, equal boundaries
  and two nonstrict contact rows.
- `VerticalStripLLT/Circular/OneBounceDNData.lean`,
  `Diagram.OneBounceDNData`: equal contact areas, area bound, contact strict
  edge, nonstrict next row, and root length/gap.
- `VerticalStripLLT/Circular/DDLocalData.lean`, `Diagram.DDLocalData`, and
  `VerticalStripLLT/Circular/NDLocalData.lean`, `Diagram.NDLocalData`: the
  two decorated variants treated explicitly above.

Related Rust: existing external `first_join_tree_lifts.rs`, option
`--first-drop-check`. The diagnostic reuses the maintained graph area
validator and the existing natural-edge model. It checks only six fixed
diagrams: no component/state enumeration and no polynomial generation.

| Area | First drop t | Root | Contact | NN deletion or forward DN target area |
| --- | ---: | --- | --- | --- |
| 012 | 2 | 02 | NN | 011 |
| 01123 | 4 | 14 | DN | 01222 |
| 01222 | 4 | 24 | DD, then DN | 01231 |
| 012333 | 5 | 25 | ND, then NN | 012332 |
| 012123 | 2 | 02 | NN | 011123 |
| 01111 | — | — | Chain base case | — |

Besides the contact conditions and exact measure change, the check verifies
valid output areas, all remaining strict corners, equality of the common
natural-edge sets, and invariance of common natural and strict edges under
the required adjacent interchange after unmarking. The fourth row resolves
the previously recorded example missing from NN/DN/DD alone. The fifth
checks that the first drop, rather than the last or the highest area, is
the stated choice.

The general proof is the first-drop argument above, not an extrapolation
from these examples. Sources and receipts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/first-drop-coverage-20260929/`.
The Rust capability check and runtime registry were inspected. No new
worker, consultant, independent review, Lean/Lake or manuscript build was
used; maintained Rust sources are unchanged.
