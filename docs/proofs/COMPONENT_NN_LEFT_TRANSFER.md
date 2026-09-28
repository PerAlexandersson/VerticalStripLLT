# Transferring the left NN overlap through a crossing corner

2026-09-28. This continues the
[NN overlap analysis](COMPONENT_NN_OVERLAPS.md). We give a four-diamond
identity, its interpretation as a transfer from a left overlap to a right
overlap, and the local reductions when the crossing corner is redundant.
These are proved local statements. Their organization into complete smaller
components remains open.

We write [P] for either the strict coloring enumerator K(P) or the HRV
elementary expression E(P). All sums are unweighted, and the same coefficients
work for both valuations. All displayed edges point forward. An arbitrary
common exterior Z is retained in every term; it includes all fixed strict
edges except those explicitly displayed.

## Valuation diamonds and actual flips

We may use an ordinary diamond as a valuation identity even when its middle
states are not actual flip neighbors. This is the unrestricted diamond from
the [auxiliary-poset note](COMPONENT_AUXILIARY_DIAMONDS.md); we recall the
short argument because the distinction is useful here.

For i<j<k with ik selected, let P_00 omit the two shorts ij,jk and let
P_10,P_01,P_11 add the indicated shorts. For colorings satisfying c_i<c_k,
at least one of c_i<c_j and c_j<c_k holds. Inclusion–exclusion gives

    [P_10]+[P_01]=[P_00]+[P_11].                    (1)

For E, write ρ(v) for the greatest vertex reachable from v in P_00.
If ρ(j)≥ρ(k), adding jk changes no reachable maximum, both before and
after adding ij. If ρ(j)<ρ(k), adding ij changes no reachable maximum,
both before and after adding jk: vertex i already reaches k. In either
case opposite terms of (1) agree. The argument includes every predecessor
of the modified tail, so it preserves the entire HRV map.

Thus (1) needs no cover hypothesis. Cover hypotheses are still essential
when we use a flip to identify component coefficients.

## The crossing corner supplied by saturation

Retain ordinary NN eligibility, with a<b=a+1<c, strict corner ac, q=ab,
and r=bc. The corner-deletion diagram is D0=L-ac. A left overlap retains
tb and exchanges ta with ab, where t<a.

If L is saturated, choose a maximal natural interval ud containing tb.
It is strict, and

    u≤t<a<b<d<c.

Indeed d=b is excluded because b is not a strict head. If d≥c, the edge
ud would properly contain the strict corner ac. This proves existence of
a crossing strict corner, but not that it starts at t or covers a given
selected state. We treat those issues separately below.

## Four diamonds

First suppose the crossing strict corner is g=td, with t<a<b<d<c. Put

    A=ta, B=tb, C=ab, D=ad, E=bd.

The symbol C in this section denotes an edge, not a component. We omit these
five edges and g from the displayed common exterior Z. The edge r=bc may
have either status in Z. With Z understood, we have

    [gBC]+[gCE]−[gAC]−[gCD]=[BDE]−[ABD].           (2)

This identity holds for arbitrary exterior Z, without cover assumptions.
Its two right-hand states lie in the smaller diagram D0-g.

Here is the complete derivation. Two diamonds retaining g give

    [gBC]+[gCE]=[gC]+[gBCE],
    [gAC]+[gCD]=[gC]+[gACD].

In their top terms g is redundant through B,E and A,D, respectively.
Subtracting therefore gives [BCE]−[ACD]. Two more diamonds, retaining D
and B, give

    [BCD]+[BDE]=[BD]+[BCE],
    [ABD]+[BCD]=[BD]+[ACD].

The top terms here have lost the redundant edges D and B. Subtracting
these equations proves (2). All four diamonds are in the existing natural
diagram or the diagram obtained by deleting the strict corner g.

## Actual paths and coefficient transfer

Now assume that the left flip

    L0=gAB  ↔  L1=gBC

is actual, and that g covers in L0. The left flip excludes Z-paths t→a
and t→b. Coverhood of g excludes Z-paths t→d, a→d and b→d, since L0
also selects A,B. There is no Z-path a→b: a,b are adjacent and C is
omitted. Thus there is no background path between any distinct pair of
t<a<b<d.

These conditions verify the covers in every diamond used above. They also
give actual paths preserving q:

    gAB ↔ gBD ↔ gDE,
    gBC ↔ gCE,
    gAC ↔ gCD.                                    (3)

The first two flips retain g and exchange A,D and then B,E. The second
line exchanges B,E while retaining g,C; the third exchanges A,D while
retaining g,C. There is an actual right-overlap flip

    R1=gCD  ↔  R0=gDE

retaining D and exchanging C,E.

Let w be the canonical NN coefficient vector. Its constancy along
q-preserving flips was proved in the overlap note. Hence its values on the
three lines of (3) are k0,kL,kR, respectively. The left and right differences
are

    ΔL=kL−k0,                ΔR=kR−k0.

Using (2), make the following change to the expression:

- subtract ΔL from both gBC and gCE;
- add ΔL to both gAC and gCD;
- add ΔL([BDE]−[ABD]) in D0-g.

The total change is zero for both valuations. The specified left difference
becomes zero and the right difference becomes ΔR+ΔL. All equalities along
the three displayed q-preserving paths are retained.

This is a transfer between two explicit pairs, not yet a transfer between
whole components. The pairs in (3) may have other incident q-preserving
flips whose coefficient equalities are broken by this change.

## When g is redundant at the left endpoint

Keep the actual left flip gAB↔gBC, but suppose g is redundant in gAB.
The same left-cover tests exclude Z-paths t→a,t→b. Every alternate
t-to-d path in Z+A+B either lies in Z or starts with A or B. Thus at
least one of the following exists:

    a Z-path t→d, a Z-path a→d, or a Z-path b→d.

If Z has a t-to-d or b-to-d path, g is redundant at both left endpoints.
We may delete it from both terms. The resulting AB↔BC is still an actual
flip in D0-g: g ends beyond b and cannot affect its cover tests.

Otherwise Z has an a-to-d path. The B-long diamond gives

    [gAB]+[gBC]=[gB]+[gABC]=[gB]+[AC].

For the last equality, B is redundant through A,C and g through A followed
by the background a-to-d path. Also [gAB]=[AB]. Therefore, for any integer
coefficients x,y,

    x[gAB]+y[gBC]=y[gB]+y[AC]+(x−y)[AB].            (4)

Only gB retains g, and it has one fewer selected edge. The other terms lie
in D0-g. This accounts for all local cases in which g is redundant at gAB.
As with (2), a recurrence for whole components still requires collecting
the terms, rather than applying component induction to isolated states.

## Moving a corner which starts earlier

Suppose g=ud with u<t<a<b<d<c. Put s=ut and h=td, retaining A,B,C,D,E
as above. Assume the left flip

    S0=Z+g+s+A+B  ↔  S1=Z+g+s+B+C

is actual, and both s,g cover in S0. We also omit h from Z; coverhood of
g already forces h to be absent. Then both g-supported flips

    S0 ↔ T0=Z+g+h+A+B,
    S1 ↔ T1=Z+g+h+B+C

are actual. Coverhood of s excludes an alternate u-to-t path; coverhood
of g excludes an alternate t-to-d path after its selected s. These give
the first vertical flip. At S1 a hypothetical new u-to-d path using C
could be replaced up to b by the common selected path u→t→b, contradicting
g's cover in S0. The other relevant tests are unchanged, so the second
vertical flip is actual too.

The left flip T0↔T1 remains actual: removing ut and adding td cannot
affect covers inside [t,b]. Moreover h covers in T0, since a bypass would
already have made g redundant in S0. Both vertical flips preserve q, and
therefore transport the canonical left difference without changing it.

We may now apply (2) to h, with g retained in the exterior:

    [g+h+B+C]+[g+h+C+E]−[g+h+A+C]−[g+h+C+D]
      = [g+B+D+E]−[g+A+B+D].                       (5)

There is an important limitation. The edges s,h are normal, because they
lie properly inside strict g. The right side omits h but retains g; it
stays in the same ambient diagram. Thus (5) supplies a local transfer,
but not an area-decreasing corner deletion. We have also not proved that
an arbitrary component supplies a covering edge ut when it is needed.

## Two choices at the same q-absent state

There is also a general reduction for competing left or right triangles.
Suppose a q-absent state P admits two distinct actual flips inserting q.
Write their retained longs as ℓ_i,ℓ_j and their selected opposite shorts
as s_i,s_j. The two new states are

    P_i=P−s_i+q,             P_j=P−s_j+q.

In P_i the edge ℓ_j is redundant through q,s_j. Indeed, the two distinct
triangles containing q have distinct opposite shorts, and neither long is
the other triangle's opposite short. Thus ℓ_j and s_j remain selected
after the first flip. Likewise ℓ_i is redundant in P_j. Consequently

    [P_i]=[P_i−ℓ_j],        [P_j]=[P_j−ℓ_i].       (6)

These deletions preserve both valuations and lower the selected-edge count.
They stay within D0: the overlap classification proves that every retained
long of a q-changing flip is normal. For a left triangle, strictness of tb
would make b a strict head. For a right triangle, ad lies properly inside
the original strict corner ac. This checks all three pair types: left–left,
right–right and left–right.

Thus simultaneous choices at one q-absent state produce lower-edge terms.
This does not yet handle a witness changing along a q-preserving flip,
nor does it turn the lower-edge states into complete components. It is a
local reduction to use when organizing the corrections, rather than an
induction on arbitrary component fragments.

## Exact checks and scope

We reused the existing Rust cover-flip model, exact strict P-partition
enumerator and HRV API. No replacement enumerator or polynomial generator
was introduced. The tests check the full coloring generating function in
the fundamental basis and the HRV expression in the elementary basis.

For source area (0,1,2,3,4,5,4), NN corner 26 and crossing strict corner 05,
the resulting deletion diagram has 18 natural edges. We enumerated only
the exterior subsets for the displayed local identities, without enumerating
its complete component graph. The exact checks passed:

| Check | Exterior selections |
| --- | ---: |
| Unconditional identity (2) | 4,096 |
| Actual four-diamond transfer and paths (3) | 1,288 |
| Redundant g at both left endpoints | 1,136 |
| The remaining redundant-g case (4) | 136 |
| Earlier-starting corner transport (5), including its actual flips | 544 |

Separate component tests expanded the previous right-overlap evidence.
All 177 components of area (0,1,2,3,4,3) pass the four-state valuation
check. In each of the two seven-vertex diagrams (0,1,2,3,4,3,2) and
(0,1,2,3,4,3,4), we tested every component left after removing disconnected
components, trees, and components with no mixed-acyclic state. There were
four and six such components, respectively; all pass. This is bounded
evidence, not a proof that the four-state correction works generally after
those reductions. The disconnected counterexample remains valid.

Receipts and frozen source are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/nn-left/`, with hashes in
`SHA256SUMS.json`. The main receipt is `seven_tall_left_complete.jsonl`;
the component tests are `six_all_boundaries.jsonl`,
`seven_unreduced_boundaries.jsonl` and
`seven_shield_unreduced_boundaries.jsonl`. The strict-edge cycle check reuses
the existing directed-acyclicity routine with strict edges reversed;
weak connectivity uses the maintained `combinatoric-core::graph::Graph` API.

Astra derived and audited the transfer, the redundant-corner cases and
the earlier-starting-corner lemma. Luna independently audited (6), including
all possible pairs of triangles. Primary checked the derivations and ran
the exact tests. No Lean build or manuscript change
was made. The next step is a rule for extending these paired corrections
along all incident flips, with whole-component reassembly and a decreasing
induction measure. The identities above do not yet supply that rule.
