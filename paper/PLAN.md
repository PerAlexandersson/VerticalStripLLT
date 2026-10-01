# Plan: component-first paper

Working title: *Flip components of vertical-strip LLT polynomials and their
elementary expansions* (P. Alexandersson, L. Dai).

Decision (user, 2026-10-01): component-first. The component theorem is the main
result. The circular expansion (open in [AS22, §6.8]) and the expansion of
[AS22] are corollaries obtained by summing over flip classes. The direct
bounce-path proof of the circular expansion is not included.

Language follows [AS22] and the authors' May note on LLT flips: decorated
unit-interval graphs, colorings κ, orientations θ with ascending edges, the
poset P₊(θ), strict P-partition generating functions K_P, the highest reachable
vertex hrv(θ,u) and λ(θ). Symmetric functions in x = (x₁, x₂, …).

## 1. Introduction
LLT polynomials; the expansion of [AS22]; the circular question in [AS22, §6.8];
the chromatic side: Stanley's orientation expansion and Hwang's flips, with his
question for LLT. Theorems A (components), B (circular expansion), Corollary C
(cumulants). The smallest flip class. Proof ideas in four paragraphs. One
sentence on the formalization. Outline.

## 2. Preliminaries
- 2.1 Symmetric functions; strict P-partitions K_P.
- 2.2 Decorated unit-interval graphs from area sequences; corners; strict edges.
  Relation with Schröder paths. Running example.
- 2.3 Colorings and G_Γ(x;q). Lemma (state expansion):
  G_Γ(x;q+1) = Σ_θ q^{asc θ} K_{P₊(θ)}.
- 2.4 Orientations, hrv, λ(θ). The expansion of [AS22].
- 2.5 Flips and flip classes. Lemma (invariants): asc, weak components and the
  selected corners are constant on a flip class. Example: the smallest class.
- 2.6 Circular graphs: integer cover, admissible orientations, circular hrv,
  circular flips.
- 2.7 Main results: Theorem 2.x (components); Corollaries (circular expansion,
  [AS22], positivity).

## 3. The four-term identity
- Lemma 3.1: adding an edge uv with hrv(v) ≤ hrv(u) does not change hrv;
  deleting a redundant edge does not change P₊.
- Lemma 3.2 (four-term identity) for K, and a pairing of the four graphs with
  equal hrv maps (so it holds for every function of the hrv map, in particular
  for e_λ and for the endpoint-marked values of §4.4).

## 4. Proof of the component theorem for ordinary graphs
Roadmap paragraph: induction on (n, |E|, moment); three smaller corrections; one
component left, completed to a layer by connectivity; NN or DN on the layer;
attachment for articulations.
- 4.1 Changing the strict marking of a selected corner (Observation).
- 4.2 Layer relations NN, DN (Proposition) from Lemma 3.2 and the adjacent
  transposition.
- 4.3 Three smaller corrections (absent corner; disconnected; no simultaneous
  corner covers with the alternating deletion formula).
- 4.4 Isolating one component (Proposition, assuming Theorem 5.1).
- 4.5 Fixing the colour of the last vertex; attachment at one vertex (Lemma).
- 4.6 Prefix and first contact (Lemmas); measure; proof of the theorem.

## 5. Connecting orientations by flips
Theorem 5.1: initial path + graph without articulation ⇒ connected orientations
with all corners covers and equal asc form one flip class.
- 5.1 Terminal labels, the graph Γ⁺ of increasing edges; preparation.
- 5.2 Crossing slides; edges between two corner chains; two chains.
- 5.3 Complete graphs.
- 5.4 Deleting a chain or an edge.
- 5.5 The last clique; the first vertex; proof of Theorem 5.1.

## 6. Circular graphs
- 6.1 Reduction to undecorated graphs.
- 6.2 Balanced subgraphs; finite deletion lemma; expansion into balanced
  subgraphs (ordered partitions; slack involution).
- 6.3 Constancy of the coefficients on a flip class; grouping.
- 6.4 A balanced class is a union of ordinary classes; proof of the circular
  component theorem.

## 7. Consequences
- 7.1 Circular expansion (sum over classes); the case of no wrapping edges gives
  [AS22].
- 7.2 LLT cumulants [DK22].
- 7.3 Questions (chromatic comparison; Schur structure of classes).

## Proof dependencies (checked against Lean, not shown in the paper)
3.2 → 4.2 → 4.4 (+ 5.1, 4.3) → 4.6; 4.5 → 4.6. 6.* uses 4.6 and 3.1 (lifted).
7.1 uses 6.4 and 2.3. Nothing in §4–§6 uses the bounce relations of [AS22].
