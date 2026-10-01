# Author revision: reader order and notation

The paper proves the circular LLT elementary expansion and then refines it to
flip components, using the same diagram relations. The introduction states
both results and explains one complete component on three vertices.

## Reader order

1. Introduction: LLT/chromatic comparison and Hwang, definitions needed for
   the two main statements, the smallest flip component, and proof ideas.
2. Circular elementary expansion: diagrams and HRV; the four original
   Alexandersson--Sulzgruber recurrences together; the shifted equivalent
   relations and their induction order; coloring and HRV proofs; intersecting contact paths; induction.
3. Ordinary components: values and flips; diamond identity; reductions to
   smaller diagrams; precise connectivity lemma (proved in Section 4);
   recurrence for a component; endpoint attachment; induction.
4. Connecting states by flips: preparation; crossing slides; complete graphs
   and two chains; deleting chains and edges; induction at the last clique
   and first vertex; proof of the connectivity lemma used in Section 3.
5. Circular components: finite expansion into balanced selections; invariance
   on components; passage to ordinary diagrams; component theorem.
6. Cumulants: published connected expansion and its component consequence.

Sections 2 and 3--5 are the two requested stages. The longer connectivity
construction is kept in the main text, after the reader has seen exactly why
its conclusion is needed. Nothing is removed from the diagram proof.

## Dependencies and notation

The connectivity lemma depends only on selected graphs and flips. It includes
an initial path attached to a graph without articulation, the precise version
used in the ordinary induction. Its deferred proof introduces no cycle.

Keep D for a diagram, A for its selected edges, C for a component, and
\mathsf{K}, \mathsf{E} for the two values. Use calligraphic letters for collections and a Greek letter
for a separate auxiliary graph when necessary. Use typewriter n/e/d for
literal path steps; NN/DN/ND/DD remain names of local configurations. Reserve
q for the polynomial parameter. Do not encode weight by shading.

Delete names for proof stages: selected-interval envelope, common-cover
uniqueness, last-clique inheritance, initial-vertex inheritance. State the
condition or operation directly. Replace "anchor" and "good" by membership
in the explicitly defined graph of edges increasing terminal vertices.
Keep genuinely useful standard terms: cover, component, articulation,
strict chain, and balanced gain graph.

Gray lies outside the path; consecutive vertices share steps; a zigzag
suppresses an arbitrary interval, possibly empty. Use the author-supplied
Robin-source snapshot and earlier Alexandersson--Dai local path figures.
Retain fully specified examples only when their selections illustrate a
construction. Generic recurrences must not be drawn as fixed small graphs.

## Checks

Check theorem/definition order, all moved labels and references, notation in
both prose and captions, native figures and exported SVGs, then compile the
assembled manuscript and inspect its introduction and diagram pages. No Lean
source or proof scope is changed in this exposition pass.

The source uniqueness proof uses size, number of east steps, and height of
the first east step (not the last). Our ordinary component proof uses
(number of vertices, total natural area, area moment); the circular aggregate
proof uses twice total natural area minus strict-edge count, then strict
ancestor-weighted edge length. These must not be conflated. The text states
the actual orders and explains why intermediate derivation diagrams need
not decrease them; only final induction targets do.
