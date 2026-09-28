# Overlapping triangles in the direct NN redistribution

2026-09-28. We continue the initial split in
[COMPONENT_NN_REDISTRIBUTION.md](COMPONENT_NN_REDISTRIBUTION.md).
We prove that only two types of target flip can change its coefficients,
and give corrections for several right-overlap cases. The compatibility of
these corrections along whole components remains open.

The subsequent [left-overlap note](COMPONENT_NN_LEFT_TRANSFER.md) supplies
a four-diamond transfer through a crossing corner, the redundant-corner
cases, and a conditional transport when that corner starts earlier.

We use unweighted valuations throughout: [P] denotes either the strict
order-coloring enumerator K(P) or the HRV expression E(P). Marking a selected
edge strict or normal does not change either valuation.

## Which flips remain

Retain the full ordinary NN hypotheses and notation from the direct split:
a<b=a+1<c, q=ab, r=bc, strict corner ac, and D0=L-ac. The map σ exchanges
a,b and fixes the other strict edges. For one complete source component C,
let h_ij(Q) indicate membership of L_ij(Q) in C. The coefficients of its
canonical image in D0 are

    w_00(Q)=0,
    w_10(Q)=h_10(Q)−h_01(Q),
    w_01(Q)=(h_00+h_01)(σQ),
    w_11(Q)=h_11(Q)+h_01(Q).                         (1)

**Claim.** These coefficients agree across every D0 flip preserving q.

The edge r is a maximal corner of D0, so no flip exchanges it. In the
00 sector the claim is immediate. In the 10 sector we add ac to lift the
flip to L_10. A maximal corner cannot enter an alternate path testing a
different natural-edge cover. Thus h_10 is constant. We may also delete q:
it is not exchanged, and adjacency prevents it from being the retained
long edge. Deletion preserves all required covers. We then add r to the
resulting L_00 flip to obtain an L_01 flip. The only natural edge properly
containing r in L is ac, and a new path using r could replace ac only if
there were an a-to-b path. There is none without q. Hence h_01 is constant.

In the 01 sector, the NN bottom swap conjugates the target flip to an
L_00 flip with exterior σQ. Adding r gives the corresponding L_01 flip,
by the same argument. In the 11 sector we add ac, which is redundant
through q,r, and then delete q to get the two source flips governing
h_11 and h_01. This proves the claim with the entire exterior retained.

Consequently, only flips exchanging q remain. Their triangles have one of
the following forms:

| Overlap | Vertex order | Retained edge | Exchanged edges |
| --- | --- | --- | --- |
| Left | t<a<b<c | tb | ta, ab |
| Right | a<b<d<c | ad | ab, bd |

For the right case, d<c follows from maximality of ac. The retained edges
in this table are normal: ad lies properly inside ac, and a strict tb
would make b a strict head, contrary to NN eligibility. These are the only
geometries requiring further redistribution; they include arbitrary exterior
selections, rather than just isolated triangles.

## The right overlap

Fix a<b<d<c. We include the other strict edges in a background T, and omit
q,r,ad,bd from T. Put

    P=T+ad,                 Q=T+ad+bd,
    U_j=D0_0j(Q),           V_j=D0_1j(P),
    B_j(T)=w(V_j)−w(U_j),   H=h_00+h_01.             (2)

The right-overlap flip V_j↔U_j is actual precisely when T has neither an
a-to-d nor a b-to-d path. Here q is adjacent, and r ends beyond d. This
condition holds for both values of j simultaneously, and also for σT.

Adding ac lifts these flips to the source, so

    h_10(P)=h_00(Q),        h_11(P)=h_01(Q).

Substituting in (1) gives

    B_0(T)=h_10(P)−h_01(P),
    B_1(T)=h_01(Q)+h_01(P)−H(σQ),
    B_0(T)+B_1(T)=H(Q)−H(σQ).                      (3)

In particular, the sum of the four defects for T and σT is zero.
To correct these four edges locally, we would add coefficient B_j(T) to
U_j(T), and likewise for σT. We next give hypotheses under which this
change has zero valuation for both K and E.

### A selected path from d to c

Suppose T has a selected d-to-c path. In U_0(T), the selected edge bd
then makes r redundant. Thus [U_0(T)]=[U_1(T)], and the same holds for
σT. Moreover, σ relabels U_0(T) to U_0(σT): both ad and bd are selected.
Both a,b are nonsinks, so this adjacent relabeling preserves the order of
reachable sinks as well as the coloring enumerator. All four valuations
are therefore equal. Equation (3) proves

    Σ_{j=0,1} B_j(T)[U_j(T)]
      + Σ_{j=0,1} B_j(σT)[U_j(σT)] = 0.           (4)

If T=σT, we use the two distinct states once, rather than duplicating
the correction. This corrects the specified boundary edges. It does not
yet assert constancy along other flips incident to these states.

### A background fixed by σ

In fact T=σT suffices without assuming a d-to-c path. Equation (3) gives
B_1=−B_0. If B_0=0, there is nothing to prove. Otherwise the initial NN
split shows that ac is redundant in L_10(P): a nonzero difference
h_10(P)−h_01(P) is impossible when ac covers.

Consider an alternate a-to-c path in T+ad+ab. If it uses ab, its suffix
gives a b-to-c path in T. If it uses ad, its suffix gives a d-to-c path
in T. If it uses neither, it lies in T, so applying σ gives a b-to-c
path in T. In every case U_0 has a b-to-c path already. Hence r is
redundant and [U_0]=[U_1]. This proves the two-state version of (4).

### A further diamond

Suppose instead that T has neither a b-to-c nor a d-to-c path. Retain the
actual right-overlap hypotheses, in particular the absence of a b-to-d
path. Define

    U=T+ad+bd+bc,           V=T+ad+bc+dc,
    B=T+ad+bc,              F=T+ad+bd+dc.

The flip U↔V retaining bc and exchanging bd,dc is actual. Indeed, the
three missing background paths are exactly what is needed to keep bd,
dc, and bc as the required covers at the two endpoints. The added ad
cannot occur in a path starting at b or d. The diamond identity, followed
by deletion of bc from its top term, gives

    [U]+[V]=[B]+[F].                               (5)

This particular rewrite decreases a finite lexicographic measure on each
term: first the number of selected edges, then the number of missing
forward comparabilities. The term B has one fewer edge. The term F has
the same number of edges as U,V, but strictly contains each of their
transitive closures. Compared with U it adds d<c; compared with V it
adds b<d. All previous relations remain, since bc follows through bd,dc.

This is a local termination observation. It does not prove that closing
the corrections under every other target flip preserves the same decrease.

## Why an unrestricted four-state correction is insufficient

Equation (4) without its hypotheses passed the first small tests, but it
is false even when the original diagram is saturated. Here is a finite
counterexample to that proposed correction, not to the component formula
or to redistribution using further diamonds.

Take area (0,1,2,3,4,3,4), strict corners {04,26}, and NN corner 26.
Thus (a,b,c,d)=(2,3,6,5). Put T={04,12}, so σT={04,13}.
The complete source component C consists of the fixed edges {04,26,12}
together with each of the following pairs:

    {23,25}, {23,35}, {23,56}, {25,35},
    {25,36}, {35,36}, {35,56}, {36,56}.

One checks the actual cover flips on these eight states: they form a
connected set and no flip leaves it. Their weak blocks are
{0,4} and {1,2,3,5,6}. Formula (1) gives

    (B_0(T),B_1(T))=(0,1),
    (B_0(σT),B_1(σT))=(0,−1).

The proposed zero correction would therefore be

    [04,12,25,35,36] − [04,13,25,35,36].

Its coefficient of x_1⋯x_7 in K is 189−147=42. The five-vertex blocks
have respectively 9 and 7 linear extensions, and the independent edge 04
contributes a factor binomial(7,2). Both E terms equal e_3 e_2².
Thus this correction cannot work simultaneously for the two valuations.

Factoring disconnected components removes this particular example. It
does not by itself prove the analogous correction for connected sources.
The failure also explains why agreement of the HRV expressions alone is
not an adequate check on a proposed redistribution.

## Exact checks and remaining step

The existing Rust probe verifies (1) on every q-preserving target flip
for all source components of areas (0,1,2), (0,1,2,3), (0,1,2,3,2),
(0,1,2,3,3), and seven selected components of (0,1,2,3,4,3).
For each selected six-vertex source component this checks 1,564 such
flips, with 416 left-overlap and 256 right-overlap flips remaining.
These are finite checks, separate from the proof above.

The saturated seven-vertex counterexample was checked independently by
complete BFS from seed 1688 (sorted full-edge mask), the maintained strict
P-partition enumerator, and the HRV API. Both the eight-state component
and the two multilinear coefficients were asserted exactly. This fixture
does not enumerate all subsets of the seven-vertex diagram.

Receipts and source hashes are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/nn-overlap/`:

- `nn_boundary_classification.jsonl`: the first three small diagrams and
  seven six-vertex components; also records nontrivial cancellations.
- `nn_saturated_attachment_audit.jsonl`: area (0,1,2,3,3).
- `nn_saturated_shield.jsonl`: the exact seven-vertex counterexample.
- `nn_unsaturated_audit.jsonl`: the smaller unsaturated precursor.

We still need a rule that propagates the corrections along whole target
components. A q-preserving flip may change the edges ad,bd or the paths
used to justify a local correction. The identities proved here do not
yet prescribe compatible coefficients after those changes. Establishing
that compatibility, or replacing these corrections by a different finite
diamond argument, is the remaining NN reconstruction step.

The left-overlap continuation also expands the exact right-overlap checks
to all 177 six-vertex components and the components surviving the known
reductions in two specified seven-vertex diagrams. These additional tests
do not establish a general correction or remove the counterexample above.

Astra independently audited the right-overlap identities, their cover
hypotheses, the two-state orbit convention, the local measure, and the
counterexample's full NN eligibility. Primary checked the arguments and
ran the independent exact Rust checks. The separate Claude consultation
on the left overlap timed out without a usable result.
