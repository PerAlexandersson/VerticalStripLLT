# Interactions between NN corrections and other flips

2026-09-28. We continue the [NN overlap analysis](COMPONENT_NN_OVERLAPS.md)
and [left transfer](COMPONENT_NN_LEFT_TRANSFER.md). We prove local reductions
for every interaction of a q-changing flip with a q-preserving flip. Their
assembly into whole smaller components remains open.

We work in the ordinary corner-deletion diagram D0 for an eligible NN step,
with q=ab and b=a+1. We write [P] for either the strict coloring enumerator
K(P) or the HRV elementary expression E(P). The same identities hold for
both. Edge sets include all prescribed strict edges unless we explicitly
pass to a corner-deletion diagram. Edge length means the difference of its
endpoints.

## Cover tests at one endpoint suffice

For i<j<k, let Z omit ij,ik,jk, and put

    P=Z+ik+ij,               P'=Z+ik+jk.

The selected pair ik,ij covers in P if and only if ik,jk covers in P'.
Indeed, either condition says that Z has no path i→j, j→k, or i→k.
For example, an alternative path to ik in P either lies in Z or uses ij,
in which case its remaining suffix is a Z-path j→k. The other endpoint
gives the same three exclusions. All paths point forward, so there are no
additional possibilities. The short edges must still be normal for this
exchange to be an actual flip.

## Commuting squares

Let f,g be actual flips at P. Write L_f,L_g for their retained longs,
x_f,x_g for the removed shorts, and y_f,y_g for the inserted shorts.
Suppose their short pairs are disjoint and neither retained long belongs
to the other's short pair. The retained longs may coincide. Put

    P_f=P−x_f+y_f,           P_g=P−x_g+y_g,
    F=P−x_f−x_g+y_f+y_g.

The two remaining sides form an actual commuting square exactly when
L_f,y_f,L_g,y_g all cover in F. Apply the preceding lemma backwards
from F to each neighboring state.

If the square fails, at least one of these selected edges is redundant.
Deleting such an edge preserves both valuations. A redundant normal edge
lowers selected-edge count in the same diagram. A redundant strict edge
instead gives a state in the diagram with that strict corner deleted.

The strict case really occurs. Take source area (0,1,2,3,4,4), with strict
corners 04,15, delete 15, and set q=12. At

    P={01,02,04,13,23},

we may retain 13 and replace 23 by 12, or retain 04 and replace 02 by 24.
Both flips are actual. The formal final state is

    F={01,04,12,13,24}.

Of the four tested edges 13,12,04,24, only 04 is redundant, through
01,12,24. Thus normal-edge deletion alone does not handle every failed
square. This example concerns a state reduction, not a component identity.

## The shared-edge possibilities

A q-preserving triangle cannot contain q: it cannot exchange q, and the
length-one edge q cannot be its long. A different triangle shares at most
one edge with the q-changing triangle. Apart from a shared retained long,
already allowed above, the possibilities are therefore:

1. Both triangles exchange the same short s. If q is absent, both remove
   s; if q is present, both insert s.
2. The q-preserving flip removes the q-changing triangle's retained long.
3. The q-preserving flip retains the other triangle's opposite short.
   Here q is absent.

In the common-insert case, write the longs as L,M and the old shorts as
q,p. Then

    P=Z+L+M+q+p,
    P_f=Z+L+M+s+p,           P_g=Z+L+M+s+q.

The long M is redundant in P_f through s,p; L is redundant in P_g
through s,q. The long L is normal by the NN overlap geometry. The long M
may be strict, so its deletion may change the diagram.

The common-remove case need not have any redundant edge at its three
states. For source area (0,1,2,3,4,3), strict corners 04,25, delete 25
and put q=23. The two actual flips at

    P={04,02,12,13}

lead to {04,02,13,23} and {04,01,02,13}. Every selected edge covers in
all three states. These are three states of a component, not a claim that
the component consists of just these states.

## A decreasing diamond identity for every pair

For any actual flip retaining L and exchanging x for y, the unrestricted
ordinary diamond gives

    [P]+[P−x+y]=[P−x]+[P−L+y].                  (1)

In the diamond's top state, L is redundant through x,y, so we delete it.
The valuation identity itself needs no cover hypothesis; actualness is
needed when we use the flip to identify component coefficients.

Both terms on the right are smaller than both endpoints. If L is normal,
use the lexicographic measure

    (number of selected edges, total selected-edge length).

The first term loses one edge. The second replaces the long by a proper
short relative to either endpoint. If L is strict, the second term belongs
to the corner-deletion diagram instead. Thus we may put raw diagram area
before these two entries to obtain a decreasing measure in every case.

Applying (1) to two flips at P and subtracting gives

    [P_f]−[P_g]
      =[P−x_f]−[P−x_g]
       +[P−L_f+y_f]−[P−L_g+y_g].                (2)

Every term is smaller than P. This covers all three shared-edge cases
without further geometric subdivisions. In the common-remove case,
P=Z+L+M+s, P_f=Z+L+M+q, P_g=Z+L+M+p, the bottom terms cancel:

    [P_f]−[P_g]=[Z+M+s+q]−[Z+L+s+p].          (3)

Relative to P_f and P_g respectively, the two terms shorten total edge
length by |q|=1 and |p|, unless deletion of a strict M already decreases
diagram area.

Suppose w is the canonical NN coefficient vector, and g preserves q.
Then w(P)=w(P_g). Set Δ=w(P_f)−w(P), R=Z+L+M and B=Z+L+s+p.
Equation (1) for g says [P]+[P_g]=[R]+[B]. We may therefore add Δ to
both P and P_g and subtract Δ[R]+Δ[B]. This preserves the displayed
q-preserving equality and makes both coefficients equal to that of P_f.
The emitted terms decrease the measure. Other incident flips may still
acquire coefficient differences; we have not proved global compatibility.

## Extending along a whole q-preserving piece

There is an exact, but incomplete, extension of (1) to a whole connected
q-preserving piece H. Choose a rooted spanning tree T with root o. For
each nonroot vertex v define, from the leaves upwards,

    c_v=δ−Σ_{u child of v} c_u,
    r=δ−Σ_{u child of o} c_u.

Matching the coefficient at each vertex proves

    δ Σ_{v in H}[P_v]
      =Σ_{v≠o} c_v([P_v]+[P_parent(v)]) + r[P_o].       (4)

Each edge sum admits (1), so the complete piece reduces to smaller states
and one explicit residual. Here

    r=δ Σ_{v in H}(−1)^dist_T(o,v).

For bipartite H this is its signed bipartition imbalance times δ; we cannot
assume it vanishes. For nonbipartite H, an odd cycle and a path to o express
2[P_o] as an integer combination of edge sums. Thus an even residual can
also be eliminated with integer coefficients. An odd residual cannot be
eliminated by integer edge sums alone: their total coefficient sum is even.

This general graph identity is independently audited, but it is not a
component recurrence. Its residual still needs treatment, and its emitted
individual states still need to be assembled into whole smaller components.

## Exact audit and remaining task

The external Rust consumer reuses the existing actual-cover model; it does
not introduce another component enumerator or modify the maintained Rust
library. It exhausts these four NN deletion diagrams:

| Source area | Deleted corner | States | One-endpoint comparisons |
| --- | --- | ---: | ---: |
| (0,1,2,3,4,3) | 25 | 2,048 | 7,168 |
| (0,1,2,3,4,4) | 15 | 4,096 | 16,384 |
| (0,1,2,3,4,3,4) | 26 | 32,768 | 155,648 |
| (0,1,2,3,4,5,4) | 26 | 131,072 | 884,736 |

All one-endpoint equivalences, square criteria, interaction classifications
and common-insert redundancies pass. These are structural checks, not a new
evaluation of K and E; equations (1)–(3) follow from the already proved
valuation diamond. Astra independently audited the paired identity, its
decreasing measure, and the spanning-tree decomposition.

Receipts and frozen consumer sources are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/nn-interactions/`, with
`interaction_audit.jsonl`, `interaction_audit.log` and `SHA256SUMS.json`.
The consumer ran with `--tall`, reduced priority and a 600-second bound,
and finished with exit zero. No Lean build or manuscript edit was needed.

The missing step remains to extend these corrections along complete
q-preserving pieces and regroup all emitted states into whole smaller
components. A decreasing identity for individual states does not establish
that step, nor does it by itself provide the decreasing diagram recurrence
requested for the manuscript.
