# Aggregate HRV identities at a fixed winding class

Status: an audited mathematical companion to the aggregate expansion, not a
Lean declaration or a proof of the general component identity. Primary found
the compatible-edge filter and finite-poset inversion; Astra audited them.
We keep the winding data separately on each weak block. This is essential:
a single ambient lattice with one shared vertical coordinate can merge the
cycle subgroups of different blocks.

## The invariant and its order

For a selected orientation A on circular vertices V with period n, let W_A
consist of the triples (u,v,l) realized by **undirected** walks along selected
edges, where traversing x→y contributes its positive natural length d_xy and
traversing it backward contributes −d_xy. Trivial walks are included. This
walk relation is not the directed reachability used to define HRV or covers.

Its connected vertex blocks are the weak blocks of A. On one such block B,
choose spanning-tree potentials z_v as in
[the lattice normal form](COMPONENT_WINDING_LATTICE.md). Then

    (u,v,l)∈W_A  iff  l∈z_v−z_u+n g_B Z,              (W)

where g_B is the gcd of its cycle windings. For g_B=0 the right side is the
singleton {z_v−z_u}. Thus W_A records exactly the blockwise winding lattices,
including the compatible potentials, rather than just their gcds.

A flip preserves W_A. The removed edge can be replaced by an undirected path
using the retained long edge and the new short edge, with the same signed
length. Conversely the inserted edge has such a path in the original state.
Substitution in any walk proves equality of the two relations.

We order these invariants by inclusion of their triples. For any W_0 arising
from a selection, the condition W_A⊆W_0 is equivalent to requiring

    (u,v,d_uv)∈W_0 for every selected edge u→v of A.    (F)

The forward implication is immediate. Conversely, W_0 is closed under walk
concatenation and reversal, so the edge conditions imply every walk condition.

## Compatible edges form a natural diagram after compression

Fix a circular diagram D and one such W_0. If a strict edge violates (F),
there are no admissible selected orientations with W_A⊆W_0. Otherwise restrict
the natural edges of D to those satisfying (F). No allowed edge joins
different weak blocks of W_0, so we may work separately on each block B.

If its g_B=0, use the ordered integer potentials z_v. Every allowed edge has
actual span z_v−z_u=d_uv∈{1,...,n−1}. Sorting and compressing the potentials
therefore turns the allowed edge set into an ordinary natural graph.

If g_B>0, put N=n g_B and choose representatives z_v modulo N. The allowed
edge condition is z_v−z_u≡d_uv mod N. Use the increasing periodic bijection
from the selected classes Λ={z_v+kN} onto the integer cover of a circle with
|B| vertices, exactly as in the primitive reduction.

In either case, natural interval closure is preserved. If an allowed long
edge contains an intermediate compressed vertex, its inverse lift lies
strictly inside the original long interval, which has span less than n.
Both original short edges are natural by interval closure of D and satisfy
the same potential condition. Their compressed images are the required
natural short edges. In the circular case no allowed span covers an entire
compressed period, since its original span is less than n≤N.

Original strict corners remain corners. A compressed natural edge properly
containing one would lift to an original natural edge properly containing
that strict corner. This contradicts its original maximality. We have
therefore obtained valid ordinary or circular decorated diagrams on the
blocks of W_0.

## The filtered semantic identity

The same fixed lift map applies to **every** selected subset of the compatible
edge set, even if it is disconnected or has a strictly smaller winding
invariant. Directed paths beginning in its chosen classes stay there. The
increasing map preserves their greatest endpoints and hence actual HRV fibers.
Finite vertex relabeling preserves strict colorings and projected acyclicity.

The allowed graph itself need not be acyclic. The orientation bijection is
between its admissible selections; cyclic selections are omitted from the
HRV model and have zero strict coloring contribution, as in the aggregate
theorem. No acyclicity hypothesis on the whole compatible graph is imposed.

Write K_A(X) for the strict order enumerator and E_A(X) for the elementary
monomial indexed by the actual HRV fibers. The already proved aggregate theorem
on each compressed block, followed by multiplication over blocks, gives

    Σ_(A : W_A⊆W_0) t^|A| K_A(X)
      = Σ_(A : W_A⊆W_0) t^|A| E_A(X).                 (Filtered)

Here A includes strict selected edges. We obtain total-edge weights by
multiplying the normal-ascent aggregate on each block by t to the number of
its strict edges. Edge counts add and both valuations factor over blocks.
All alphabets, including the empty one, are covered. We have used no
component formula and no symmetry assumption on an individual component.

## Exact winding classes by finite-poset inversion

For fixed D there are finitely many admissible selections, hence finitely
many realized invariants W_A. Let P be this finite poset, ordered by inclusion.
It need not be closed under arbitrary unions, intersections or subrelations.

For each W∈P, define its defect polynomial

    Δ_W(t,X)=Σ_(A : W_A=W) t^|A| (K_A(X)−E_A(X)).

Equation (Filtered) says Σ_(W≤W_0) Δ_W=0 for every W_0∈P. Inducting over P
and subtracting all strictly smaller terms proves Δ_W=0 for every exact W.
Thus the aggregate HRV formula holds separately at each exact blockwise
winding invariant and each selected edge count.

Each such class is a union of entire flip components. The conclusion is an
identity for that union; it does not assume or imply equality for every member
component separately. In the connected primitive case g=1, the edge filter
before inversion is all of D. Inversion subtracts proper winding classes and
isolates the primitive sector collectively.

## Same primitive invariant does not identify a component

A stronger obstruction than isolated chain states occurs in the saturated
four-vertex diagram of area (3,1,2,3), with strict edges S={10,03}. Writing
only the additional normal edges, it has the two entire components

    C₃ = {{02,12}, {12,23}, {20,23}},
    C₄ = {{13,02}, {13,12}, {13,20}, {13,23}}.

They are connected and active at normal ascent 2; every strict edge is a
lifted cover in every displayed state. Both have winding gcd 1 and the same
connected walk relation W. For C₃ compare 1→0→2, of length 5, to 12, of
length 1. For C₄ compare the strict path 1→0→3, of length 6, to 13, of
length 2. The invariant transports these winding data across each component.
The natural underlying undirected graph is complete and has no articulation.

The legal flip graph on C₃ is the displayed three-state path: first use
0<2<3 retaining 03, then 1<2<4 retaining 10. In C₄ the legal exchanges are
02↔23 retaining 03, 12↔20 retaining 10, and 12↔23 retaining 13. These form
a four-state path. The only other natural normal edges are 01 and 30, both
inadmissible because they oppose strict edges. Changing the status of 13
would exchange it with one of those inadmissible edges. Inspecting the
remaining possible triangles gives no other neighbors. This establishes
entire-component scope independently of the finite computation below.

No displayed state has a projected order that is a union of chains. Their
HRV sums are different:

    E(C₃)=e₃e₁+2e₄,       E(C₄)=2e₃e₁+2e₄.

The partitions in the displayed C₃ order are (3,1),(4),(4); for C₄ they
are (3,1),(3,1),(4),(4). Thus discarding chain-only components does not
restore uniqueness, and equality of the invariant does not even force the
same HRV polynomial.

These examples do satisfy the formula; their distinction is not a
counterexample to it. For a direct all-alphabet check, color the common strict
chain 1→0→3 by a<b<c and color vertex 2 by y. The three C₃ states contribute
conditions y>b, a<y<c, and y<b respectively. Their summed indicator is

    1 + [a<y<b] + [b<y<c].

Summing over colors and vertex weights gives e₃e₁+2e₄. In C₄ the edge 13
is implied by the strict chain; the four remaining conditions are y>b,
y>a, y<b, and y<c. Their sum is

    2 + [a<y<b] + [b<y<c],

giving 2e₃e₁+2e₄. These equalities also cover repeated colors and empty
alphabets. They verify the exact diagnostic, not a general isolation lemma.

## Exact check and remaining target

The complete component lists were checked with the existing Python
`probe.model` and the existing Rust `component_source_probe` binary, without
rebuilding or adding a flip implementation. Rust input records were

    4 3 1 2 3 30 100 1
    4 3 1 2 3 60 100 1

They return respectively 3 and 4 states, with 2 and 3 flip edges. The
maintained `circular_highest_reachable_vertices` routine, via the existing
Rust bridge, independently confirms all seven HRV partitions. The source
companion checks also pass; those checks are not substitutes for the direct
coloring identities above.

External receipt in `diamond-exploration/` under the project requests root:
`primitive_nonchain_counterexample.json`, SHA-256
`fbb0067e069f297ba7141fdc6c856677c7d9f1efbf09a786769fd5dbf762921f`.
Reused Python model SHA-256:
`6f4517aca6cfdfa5b802a05edc5ffef24fb245a9ab568d5c5b0abadde4494db4`;
reused Rust probe source SHA-256:
`97f22d7076b56a8f5ec46742503b363be22d8802768b68958a9617b6dca51f72`.
The short Python invocations only assembled inputs and compared existing
models; they introduced no new polynomial generator or component algorithm.
An earlier, weaker two-singleton obstruction is retained in
`primitive_lattice_counterexample.json`, SHA-256
`2d9e2aef0201fc4865096fefb362ab3f70dc148e81bebf3d1eedb12402e7f6e0`.

The remaining task is component isolation within a fixed invariant class,
using genuine recurrence relations or a cancellation companion. Exact winding
classes give more available identities, but the counterexample prevents
replacing this task by a uniqueness assertion on those data alone.

Related Lean: `Circular/Expansion.lean` and `Expansion.lean` supply the
aggregate inputs; `Circular/Flip.lean` and `Circular/ComponentSemantics.lean`
fix the complete-component target. Compression and finite-poset inversion
in this note are not yet formalized.
