# Four-edge cases and complete component reconstruction

2026-09-28. We give a sixteen-row NN case table, repair its incomplete
component coefficients, and prove a second reconstruction which remains
valid with exterior components attached at the two ends of a four-vertex
block. These are proved cases of the requested recurrence argument. We
have not established its general component-reconstruction step.

The table below is a new explicit calculation. We have not identified it
with the sixteen-case example recalled by the author. The archived manuscript
contains case-based recurrence sketches, but we did not find an explicit
sixteen-case table there.

## A four-edge split

Take the complete natural diagram on 0,1,2,3, with strict corner f=03. Put

    a=01, b=02, c=12, d=13, e=23, f=03.

Consider its complete five-state component

    C5={fabc,fabd,fbcd,fbde,fcde}.

As usual, [P] denotes either the strict coloring enumerator K(P) or the
HRV elementary expression E(P). The same coefficients work for both.
Let D0 be the diagram with f deleted; all its five edges are normal.

For the NN move at 0<1<3, use the four bits

    (q,r,p,s)=(a,d,b,c).

We keep the orientation of e as exterior data. Thus there are sixteen
cases for each fixed exterior orientation. Each pair in the table records
the cases e absent and e selected, in that order. The source coefficient
h is membership in C5. The coefficient w is the canonical NN image from
[the direct split](COMPONENT_NN_REDISTRIBUTION.md). Explicitly,

    w(0,0,p,s)=0,
    w(1,0,p,s)=h(1,0,p,s)−h(0,1,p,s),
    w(0,1,p,s)=h(0,0,s,p)+h(0,1,s,p),
    w(1,1,p,s)=h(1,1,p,s)+h(0,1,p,s).

The omitted e-status is unchanged in each equation. The swap of vertices
0,1 exchanges p,s and fixes e. The column g includes the single repair
proved below.

| qrps | Source h | NN image w | Repaired g |
| --- | --- | --- | --- |
| 0000 | (0,0) | (0,0) | (0,0) |
| 0001 | (0,0) | (0,0) | (0,0) |
| 0010 | (0,0) | (0,0) | (0,0) |
| 0011 | (0,0) | (0,0) | (0,−1) |
| 0100 | (0,0) | (0,0) | (0,0) |
| 0101 | (0,1) | (0,1) | (0,1) |
| 0110 | (0,1) | (0,1) | (0,1) |
| 0111 | (1,0) | (1,0) | (1,1) |
| 1000 | (0,0) | (0,0) | (0,0) |
| 1001 | (0,0) | (0,−1) | (0,−1) |
| 1010 | (0,0) | (0,−1) | (0,−1) |
| 1011 | (1,0) | (0,0) | (0,0) |
| 1100 | (0,0) | (0,0) | (0,0) |
| 1101 | (0,0) | (0,1) | (0,1) |
| 1110 | (1,0) | (1,1) | (1,1) |
| 1111 | (0,0) | (1,0) | (1,0) |

## One correction completes two components at once

The complete components of D0 needed here are

    D1={abd,bcd,bde},           D2={abcd,abde,bcde},
    D4={abe,bce},               D5={cde}.

Checking the only two natural triangles, 012 and 123, proves that these
sets are complete components. The states ace and acde are also singleton
components. The NN image in the table is

    X(C5)=X(D1)+[cde]+[abcd]+[abde]+[acde]−[abe]−[ace].       (1)

Only D2 and D4 have nonconstant coefficients: respectively (1,1,0) and
(−1,0). The edge d=13 is redundant whenever c=12 and e=23 are selected.
Consequently we may add the zero expression

    [bcde]−[bce]=0.                                           (2)

This fills the missing positive coefficient of D2 and the missing negative
coefficient of D4 simultaneously. These are precisely the two changed
entries of the table. The repaired coefficients are constant on every
complete component of D0. Finally [acde]=[ace] by the same redundancy, so

    X(C5)=X(D1)+X(D2)−X(D4)+X(D5),             X=K,E.          (3)

Every term is now a whole component in a strictly smaller diagram.
This is a shorter repair of the canonical NN image than the earlier
three-diamond derivation from a different initial split. Redundancy is
exactly the simplification of the top state used in a paired diamond;
we do not introduce a statewise equality between unrelated orientations.

Formula (3) also holds with any complete exterior component Ω attached
only at vertex 3. For each exterior state Z, the NN swap of 0,1 fixes Z;
all other steps are diamonds or redundant-edge deletions with Z retained.
The actual flip graphs factor across this single articulation. Thus (3)
holds with C5 and each D_i replaced by its Cartesian product with Ω, and
all four targets are complete components in the corner-deletion diagram.
This includes cyclic exterior components. We sum valuations on the unions
of the states, counting vertex 3 once, rather than multiplying polynomials.

## A repair compatible with exterior components

There is a second useful reconstruction in the original diagram. Its
complete eight-state tree component is

    C8={fab,fac,fae,fbc,fbd,fcd,fce,fde}.

Pair these states by the four actual flips

    (fac,fcd), (fbc,fce), (fab,fbd), (fae,fde).

The paired diamond from
[the interaction note](COMPONENT_NN_FLIP_INTERACTIONS.md) gives

    [fac]+[fcd]=[fc]+[acd],
    [fbc]+[fce]=[fc]+[bce],
    [fab]+[fbd]=[fb]+[abd],
    [fae]+[fde]=[fe]+[ade].                                  (4)

The four f-deleted terms do not yet have constant component coefficients.
Relabeling the adjacent vertices 1,2 sends abd to abe. Vertex 1 is a
nonsink in abd, so this relabeling preserves the order of the sinks and
therefore both valuations. After this repair, (4) becomes

    X(C8)=2X({fc})+X({fb,fe})
           +X({acd,ade})+X({abe,bce}).                       (5)

Every brace is a complete component. The first two belong to the original
diagram and have disconnected selected graphs. The last two belong to D0.
Thus the first two are covered by vertex induction on the disconnected
blocks, and the last two by area induction.

We can retain an arbitrary exterior in this argument. Suppose these four
consecutive vertices form a complete natural block, the exterior meets it
only at 0,3, and there is no exterior undirected path joining 0 to 3.
The edge 03 remains a strict corner. Every natural triangle lies entirely
in the block or entirely in the exterior. A path leaving either part cannot
return to change an internal cover test: a return through the other endpoint
would supply the excluded exterior path. Hence the full flip graph is the
Cartesian product of the two flip graphs.

Let Ω be any complete exterior component, possibly with cyclic selected
graphs. For each Z in Ω, the four identities (4) hold with Z included in
every state. The swap of 1,2 fixes Z, so its repair also holds with Z.
Summing gives (5) with each component replaced by its Cartesian product
with Ω. Each product is again a whole component in the indicated diagram.
The first two outputs still disconnect the interior pair {1,2}, or vertex
1, respectively, from the remaining vertices. This proves a uniform
recurrence for these components, including examples with cycles elsewhere.

The products here are products of state sets, and [Z+P] is evaluated on
their union with each shared vertex counted once. We do not multiply the
two polynomials at an articulation vertex.

For a more general exterior, the relabeling instead gives

    [Z+abd]=[σZ+abe],             σ=(1 2).

One must then prove that the relevant exterior families reassemble after
σ. That condition cannot be replaced by assuming Z=σZ.

## Verification and scope

Astra independently checked (1)–(5), the target component lists and the
exterior restriction. The Rust consumer checks all sixteen rows in both
e-sectors for C5 and C8, the canonical images on K and E, and the repair
(2) on every target flip. It also checks all component lists and both
valuations in three instances of (5):

- the isolated four-vertex block;
- two four-vertex blocks meeting at an endpoint, with Ω the five-state
  cyclic component in the other block (40 source states);
- a four-vertex block with a pendant edge attached at each endpoint.

For (3), a further check attaches another five-state cyclic component at
vertex 3. Its 25-state source reconstructs into complete components of
sizes 15,15,10,5, with coefficients 1,1,−1,1. Both valuations agree exactly.

The maintained strict P-partition and HRV APIs perform the two exact
valuation checks. The source reuses the existing actual-flip enumerator.
Receipts and frozen sources are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/component-reassembly/`,
principally `nn_four_bit_pieces.jsonl`, its log and `SHA256SUMS.json`.
No manuscript or Lean source is changed.

The remaining problem is to construct and close these repairs for arbitrary
exterior orientations in every decreasing recurrence. The examples show
complete reconstruction after the first pieces fail to fit; they do not
prove that all such reconstructions exist.
