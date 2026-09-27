# Winding lattice and primitive circular components

Status: audited mathematical reductions, not Lean declarations. The primary
proposed the edge-vector invariant and the finite-cover reduction; Terra
proved the lattice normal form and supplied the higher-winding family. Astra
independently audited the entire-component transport and its HRV semantics.
These reductions do not prove the remaining component formula.

## An integer lattice preserved by every flip

Work first in the complete circular diagram U_n. The
[ambient reduction](COMPONENT_AMBIENT_REDUCTION.md) permits this without
changing any original complete decorated component or its unweighted sums.
For a selected edge u→v of natural length d_uv∈{1,...,n−1}, put

    b_uv = (e_v−e_u, d_uv) ∈ Z^V ⊕ Z.

Let L(A) be the integer span of these vectors. In a lifted triangle a<b<c<a+n,
the long vector is the sum of the two short vectors. Thus exchanging ab and
bc while retaining ac replaces {b_ab,b_ac} by {b_ac,b_bc}, with the same
integer span. Every actual flip preserves L(A). It also preserves the weak
vertex partition, so we may retain a separate lattice for each block.

Fix a connected selected block B and choose an undirected spanning tree T.
Choose a root lift and propagate integer potentials z_v along T: traversing
u→v adds d_uv, and traversing it backward subtracts d_uv. Then z_v≡v mod n.
Write R_B={x∈Z^B : Σ_v x_v=0}. The tree-edge vectors generate precisely

    Γ_z = {(x, Σ_v z_v x_v) : x∈R_B}.

For a chord u→v, subtracting its tree path leaves the vector

    (0, d_uv−(z_v−z_u)) = (0, n w_uv).

The integers w_uv are the signed windings of fundamental undirected cycles.
Let g be the gcd of their absolute values, with gcd of an empty or all-zero
list equal to zero. We obtain the exact normal form

    L(A) = Γ_z + (0, n g Z).                           (WL)

In particular, L(A)∩(0⊕Z)=0⊕ngZ. The subgroup, and hence g, is independent
of the spanning tree and invariant throughout the entire component. The
potentials modulo ng also matter when g>0; the gcd alone does not generally
specify the embedded lattice. No converse connectivity assertion is made.

When g=0, all selected edges satisfy z_v−z_u=d_uv: these are precisely the
compatible integer lifts in the existing balanced-to-ordinary reduction.
When g>0, they satisfy that equation modulo ng. More generally, compatible
potentials modulo hn with the prescribed residues exist exactly when every
cycle winding is divisible by h. This follows by the same spanning-tree
construction and chord test. Thus h|g is the exact condition, with every
positive h allowed in the balanced case.

## Higher winding occurs in admissible orientations

Projected acyclicity does not force g≤1. In U_4, take

    0→3→2→1, together with 0→1.

The path has lifted length 9 and the shortcut length 1. Their difference is
8=2·4, and the unique undirected cycle has winding 2. The projected graph is
a DAG. Every edge has legal natural length at most 3.

For general n≥4, the path 0→n−1→n−2→...→1 together with 0→1 has winding
n−2, since its path length is (n−1)² and the shortcut has length 1.
These are exact symbolic families, not finite experimental evidence.

## Compressing the finite cover

Suppose a connected selected block B has m vertices and g>0. Keep the original
ambient period n and set N=ng. Choose representatives z_v∈[0,N) of the
compatible potentials modulo N. They are distinct, since their residues
modulo n are the distinct original vertices. Let

    Λ = {z_v+kN : v∈B, k∈Z}.

Every selected step preserves Λ: starting from a lift of u in Λ, adding d_uv
ends in the chosen congruence class of v modulo N. Consequently every selected
directed path starting in Λ stays there. The same statement holds for
traversing selected edges backward as an undirected walk.

List the representatives z_v in increasing order and let r(v)∈{0,...,m−1}
be their ranks. There is an increasing bijection

    F : Λ → Z,      F(z_v+kN)=r(v)+km.

Each selected step has positive original span d_uv<n≤N, so its compressed
span is an integer in {1,...,m−1}. Its image is therefore a legal natural
edge of U_m. The resulting projected selected graph is simply the original
graph with its vertices relabeled by r; acyclicity is preserved.

All selected paths and their lifted endpoints correspond under F. In
particular, lifted cover conditions and greatest reachable lifts correspond.
Intermediate integer points outside Λ cause no problem: they are unreachable
from Λ. HRV fibers are carried by the vertex bijection r, and strict colorings
are carried by relabeling vertices. Both K_A and E_A are preserved.

## Transport includes the entire component

An original flip can be translated so that its retained long edge begins in
Λ. Its selected fork or join then forces all three triangle lifts to lie in
Λ. Compression gives an actual flip with long span less than m.

Conversely, begin with the compressed state and follow an arbitrary flip
path in U_m. Maintain the following property: every selected edge, lifted
back by F, has positive original span less than n. This holds initially.
In the next flip, both new short edges lie inside its retained selected long
edge. Their inverse images therefore lie inside the original long interval,
whose span is less than n. They again have legal original lengths. The
corresponding covers and projected admissibility have already been preserved,
so this is an actual original flip. The property holds at the next state.

Induction along the flip path proves that compression identifies the original
complete component with an **entire** component in U_m, preserving both
component sums. It is not merely an embedding into a larger component.
The inverse map need not be defined on every orientation of U_m at once;
the retained-long-edge invariant supplies it on the full reachable component.

## The compressed winding is primitive

An original closed undirected walk has total signed displacement n w. By
(WL), g divides w. Its lift in Λ ends N(w/g) above its starting point.
Since F(x+N)=F(x)+m, the compressed walk has displacement m(w/g), hence
winding w/g. Applying this to fundamental cycles shows that the gcd of the
compressed cycle windings is exactly 1.

Thus every connected unbalanced component is semantically equivalent to an
entire **primitive** circular component, meaning one with winding gcd 1.
For g=1 on the full vertex set the construction simply recovers the original
circular order; it does not solve primitive components.

Weak blocks can be treated independently. Every flip lies within a block,
and covers and paths between its vertices are internal. The full component
is a Cartesian product of its block components. Both valuations factor over
these blocks; compression orders all of a block's lifted vertices and
preserves its greatest reachable endpoints even if original blocks interleave.

The full goal therefore reduces to two connected families: ordinary
components (balanced blocks), and primitive circular components (unbalanced
blocks). Forests are already settled by the
[connected aggregate companion](COMPONENT_CONNECTED_AGGREGATE.md). Equality
of lattice invariants does not itself isolate a component, and neither
remaining family with undirected cycles is proved here.

The subsequent [exact winding companion](COMPONENT_LATTICE_AGGREGATE.md)
proves the aggregate identity separately at every blockwise signed-walk
invariant. Keeping the entire undirected walk relation avoids merging cycle
subgroups from different blocks into one shared vertical coordinate. This
semantic refinement still does not isolate individual components.

Related Lean: `Circular/HRV.lean`, `Circular/LiftCover.lean`, and
`Circular/Flip.lean` fix the selected-edge and actual flip semantics. The
lattice and cover-compression lemmas above are not yet implemented.
