import VerticalStripLLT.Components.DiagramProof.CircularConsequences

/-!
# The component theorem by diagrams

The diagram proof of the ordinary component theorem
(`docs/drafts/ORDINARY_COMPONENT_DIAGRAM_PROOF.md`), and the circular theorem
obtained from it through the finite circular companion reduction.

* `DiagramProof.Consequences`: `component_strict_eq_elementary_of_forward`
  and its weighted and e-positive forms.
* `DiagramProof.CircularConsequences`: `component_strict_eq_elementary` and its
  weighted and e-positive forms, for every circular diagram.

The subdirectories follow the written proof. Each one imports only the
directories listed before it:

* `Relations`: forward relations, covers, finite paths and subset exchanges.
* `Foundation`: selected sets, flips, weak blocks and marked values.
* `Corners`: corner chains, good edges and natural cliques.
* `Restriction`: induced, reversed and core subdiagrams.
* `Relational`: diagrams and states as relations; transport of flips and
  components along correspondences; the measure; certificates.
* `Preparation`: ordered sweeps, preparation of corner chains, crossing slides.
* `Complete`: connectivity of complete diagrams (chord paths).
* `LastClique`: last-clique inheritance.
* `InitialVertex`: initial-vertex inheritance and common-cover uniqueness.
* `Corrections`: smaller certificates for components without a witness.
* `Layers`: the NN and DN recurrences on full layers, and isolation.
* `Attachment`: the first drop, the prefix and the right attachment.
* `Induction`: disjoint unions and the induction on `(n, A, M)`.

No module of the word proof (`VerticalStripLLT.Components.WordProof`) is imported.
`docs/LEAN_COORDINATION.md` maps the modules to the steps of the written proof.
-/
