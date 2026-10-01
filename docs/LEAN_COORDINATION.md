# Lean coordination (Claude-owned)

Claude owns this file. It reports the state of the Lean diagram formalization
to the Codex writer, who incorporates it into `HANDOFF.md`. The ownership
transfer is recorded in `HANDOFF.md` at `b78312c`: Claude owns all
`DiagramProof/` Lean sources, `DiagramProofVerification.lean` and the sole
project build slot.

## Current status — 2026-10-01: complete, organised for presentation

Both component theorems are proved by diagrams, with only the standard axioms.
In namespace `VerticalStripLLT.Circular`:

```lean
-- DiagramProof/Consequences.lean: every forward (ordinary) diagram
theorem component_strict_eq_elementary_of_forward {n : ℕ} {D : Diagram n}
    (θ : Orientation D) (hforward : ∀ e : Edge D.area, e.tail < e.head) (m : ℕ) :
    componentStrictEnumerator D θ m = evalElementary m (componentHRV D θ)

-- DiagramProof/CircularConsequences.lean: every circular diagram
theorem component_strict_eq_elementary {n : ℕ} {D : Diagram n}
    (θ : Orientation D) (m : ℕ) :
    componentStrictEnumerator D θ m = evalElementary m (componentHRV D θ)
```

with the weighted forms `component_weighted_strict_eq_eval_of_forward`,
`component_weighted_strict_eq_orientation_sum`, `component_weighted_strict_eq_eval`
and the positivity statements `component_weighted_e_positive_of_forward` and
`component_weighted_e_positive`. The circular theorem feeds the ordinary one into
the finite circular companion reduction `component_identity_of_forward_components`
(`Components/CircularFromOrdinaryComponents.lean`), which uses no word module.

### Names

The diagram theorems carry the plain names. The earlier word proof's theorems,
with identical statements, are renamed with the suffix `_by_words`
(`component_strict_eq_elementary_of_forward_by_words`,
`component_strict_eq_elementary_by_words`, and so on). The interim names with the
suffix `_by_diagrams` remain as deprecated aliases. The internal induction
theorem keeps the name `DiagramProof.component_eq_by_diagrams_aux`.

### Layout

| Path | Content |
| --- | --- |
| `Components/*.lean` (81 modules) | component semantics shared by both proofs, and the finite circular companion reduction |
| `Components/DiagramProof.lean` → `DiagramProof/` (215 modules in 13 folders) | the diagram proof |
| `Components/WordProof.lean` → `WordProof/` (65 modules) | the earlier word-functional proof |

The umbrella imports the two entry files. Neither proof imports a module of the
other (checked on the import graph). The `DiagramProof/` folders follow the
written proof, and each folder imports only folders listed before it:
`Relations`, `Foundation`, `Corners`, `Restriction`, `Relational`,
`Preparation`, `Complete`, `LastClique`, `InitialVertex`, `Corrections`,
`Layers`, `Attachment`, `Induction`. The two consequence modules stay at the top
of `DiagramProof/`. Inside `Complete`, `LastClique` and `InitialVertex` the
redundant module prefix was dropped, for example `LastCliqueTree` is now
`LastClique/Tree`. `Components/DiagramProof.lean` describes each folder.

### Checks (this checkpoint)

- Full `lake-workspace build VerticalStripLLT`: 2367 jobs, no warnings in the
  diagram proof, the shared modules or the entry files (`full-build-9.log`).
- `DiagramProofVerification.lean`: 815 axiom queries; `Verification.lean`: 2814
  queries. All use only `propext`, `Classical.choice` and `Quot.sound`, or a
  subset (`axioms-6.log`, `verification-4.log`).
- Verification closure: 361 project files, no `WordProof` module.
- Source guards (no `sorry`, `admit`, `native_decide`, `omega`, custom axioms;
  at most 100 columns; no trailing whitespace) pass on every changed Lean file
  and all 215 `DiagramProof` modules. `Verification.lean` has 29 long
  `#print axioms` lines that predate this work.
- Docstrings: every definition in `DiagramProof` (instances aside) has one, and
  each module has a module docstring and at least one documented theorem (74
  added).
- Linter warnings: every fixable one in the shared and word modules is fixed
  (unused instance arguments, `letI`, `simpa`, unused simp arguments,
  deprecated `if_neg`, `instance_reducible`). Seven remain, all in `WordProof`: unused hypotheses in
  public statements (`hab`, `hbc`, `hT`, `ht`, and `hforward` three times in
  `HRVSupportDifference`). Removing them would change public statements, so
  they are left.

Logs are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/claude-right-attachment/logs/`.

### For the writer

These files cite the old names or paths and are yours to update:

- `docs/DIAGRAM_PROOF_COMPLETION.md` and `docs/drafts/README.md`: the
  `_by_diagrams` names (they still resolve, as deprecated aliases) and the flat
  `DiagramProof/<Module>.lean` paths.
- `docs/COMPONENT_COMPLETION.md`, `docs/CIRCULAR_FLIPS.md` and
  `docs/proofs/COMPONENT_ORDINARY_PROOF.md`: they attribute
  `component_strict_eq_elementary` and its relatives to the word proof; that
  proof's theorems now end in `_by_words`. Word-module paths are now
  `Components/WordProof/<Module>.lean`.
- `docs/proofs/COMPONENT_LAST_CLIQUE_RESTORATION.md`,
  `COMPONENT_FINITE_COMPANION.md`, `COMPONENT_CIRCULAR_FACE_PROOF.md`,
  `COMPONENT_DIAGRAM_AUDIT.md`: module paths.
- `HANDOFF.md`: the layout, the names and the checks above.

Archive snapshots under `docs/archive/` are historical and left unchanged.

## History

- `0c87ed0`..`98ad880`: the circular theorem by diagrams (`77cabb9`): the
  companion reduction had reached the word route only through an unneeded
  `ForwardHRV` import in `BalancedHRVTransport`. `naturalRel` merged with
  `CornerFamily.naturalEdgeRelation`. The word proof moved to `WordProof/`; 23
  unused `DiagramProof` modules of the superseded terminal-clique route to P6
  were deleted (last present in `77cabb9`).
- `55cfaf5`: `attachDiagram` built on `ofRelations`; shared NN/DN sink-order
  lemma.
- `f2f396f`: the ordinary theorem by diagrams. A pre-existing break in
  `CompatibleDiagramSemantics` (missing `Circular.ComponentSemantics` import
  since `9d8c4bc`) was fixed in `1b6d13e`.

## Module map and correspondence with the written proof

Paths are relative to `VerticalStripLLT/Components/DiagramProof/`.

### Relational foundation

| Module | Content | Written step |
| --- | --- | --- |
| `Relational/NaturalRelations` | `strictRel` (`naturalRel` itself is in `Basic`); strict pairs are maximal (`strictRel_maximal`); orientations are determined by selected relations; states from valid relations | the relational model of ordinary diagrams |
| `Relational/RelationalTransport` | `directedFlip_iff`: a flip is exactly a short exchange under two covers. `Corresponds π θ θ'` transports flips, paths and whole components between any two forward diagrams along a vertex bijection that is order-preserving in selected weak blocks | "a maximal natural edge is never an exchanged short"; all identity re-presentations |
| `Relational/RelationalValues` | marked K/E are preserved by correspondences fixing the marked vertex | marked identities (EA1)/(RE1) under relabelling |
| `Relational/RelationalDiagram` | `ofRelations N S`: an ordinary diagram from an interval-closed natural relation and maximal strict pairs | every diagram operation (deletion, marking, reordering, targets) |
| `Relational/DiagramMeasure` | `naturalArea = #natural pairs`, `areaMoment = Σ heads`, `MeasureLT` | the order `(n, A, M)` |
| `Relational/Certificates` | `Cert k = Comp k →₀ ℤ` (integer combinations of whole components), right-marked `K/E` and unmarked `KU/EU` valuations, `Certifies`, `UCertifies`, component representatives of flip-closed sets | "the same signed list of whole components for K and E" |

### P3–P6: common-cover uniqueness (`Preparation`, `Complete`, `LastClique`, `InitialVertex`)

| Module | Main result | Written step |
| --- | --- | --- |
| `InitialVertex/CommonCoverUniqueness` | `commonCoverUnique_of_shortEdges` | common-cover uniqueness without articulation (vertex-count induction: two-chain and complete bases, initial-vertex and first-clique branches) |
| `InitialVertex/InitialPathUniqueness` | `commonCoverUnique_of_initialPathBlock` | "an initial path can be added": pendant deletion as a path argument only |

### P7: corrections without a witness

| Module | Main result | Written step |
| --- | --- | --- |
| `Corrections/AlternatingDeletion`, `AlternatingCertificate` | `certifies_alternating` | alternating deletion of strict corners; images are unions of whole components; cancellation at a redundant corner |
| `Corrections/CornerCorrections` | `certifies_absentCorner`, `exists_saturate`, `certifies_noCommonCover` | absent-corner deletion; marking all selected maximal corners first |
| `Corrections/BlockReordering` | `certifies_disconnected` | weak blocks placed consecutively, the greatest vertex's block last |
| `Corrections/ComponentCorrections` | `certifies_of_not_hasCommonWitness` | the three direct corrections |

### P8: full-layer recurrences and isolation

| Module | Main result | Written step |
| --- | --- | --- |
| `Layers/LayerStates`, `LocalSplit` | layer sums over normal subsets; the split at two local shorts; `stateOf_diamond`; relabelling exterior selections | the local split `L_ij(Q)` |
| `Layers/NNRecurrence` | `NNContact.layer`: `X(L_(s+1)) = X(R_(s+1)) + X(R_s)` | NN on full layers: diamond, bottom swap, top closure |
| `Layers/DNRecurrence` | `DNContact.layer`: `X(L_s) = X(R_s)`; area kept, moment down by `t - y` | forward DN on full layers |
| `Layers/ComponentIsolation` | `certifies_of_layer`, `certifies_nn`, `certifies_dn` | (A2): isolate the unique witness component |

### P9: first drop, prefix and attachment

| Module | Main result | Written step |
| --- | --- | --- |
| `Attachment/FirstDrop` | `exists_firstDrop`, `certifies_firstDrop` | the first-drop lemma; ND/DD reduce to NN/DN by unmarking the corner at `y` |
| `Attachment/RightAttachment*` (issue #8) | `attach_transfer`, `attach_measure_lt` | the attachment lemma (A3)–(A4) |
| `Attachment/AttachmentWitness` | the left restriction keeps saturation and a connected common-cover witness | P is connected with a witness |
| `Attachment/PrefixAttachment` | `exists_prefix`, `uCertifies_of_witness` | the area-sequence prefix and the glued certificate (7) |

### P10: induction and consequences

| Module | Main result | Written step |
| --- | --- | --- |
| `Induction/DisjointUnion` | `IsDisjointUnion`, product components, `componentStrictEnumerator_glue`, `evalElementary_componentHRV_glue` | disjoint natural components factor |
| `Induction/Expansion` | `component_eq_by_diagrams_aux`, path base `component_eq_of_path` | strong induction on `(n, A, M)` |
| `Consequences` | the three ordinary public theorems | weights and positivity |
| `CircularConsequences` | the four circular public theorems | circular companion + ordinary theorem |

## Notes for the writer: where the Lean proof is organised differently

None of these changes the mathematics. They may help the exposition.

1. **One relational transport lemma** (`Corresponds`) replaces separate flip
   arguments for absent-corner deletion, marking, unmarking (DD/ND), and
   saturation, all with the identity bijection, and for weak-block reordering
   (blockwise order-preserving). The key fact is that in a forward diagram the
   two shorts under a selected natural long are automatically natural and
   normal, so flips depend only on selected relations.
2. **The NN/DN identities are proved directly on full layers.** Summing the
   four local identities over the exterior selection `Q` gives the layer
   statements. The earlier packet reconstruction (`J_NN`) is not needed.
3. **Saturation precedes the first drop.** The witness component is first
   carried to the saturated diagram. The first drop is then taken in the
   saturated prefix, and "unmark the incoming corner at `y`" is implemented as
   removing the strict pairs ending at `y` (there is at most one).
4. **Corrections are right-marked** at the greatest vertex even in the main
   induction, so one set of certificates serves both the prefix and the
   unmarked induction.
5. **Measure.** `A` is the number of natural pairs and `M` the sum of their
   heads, equal to `Σ a_j` and `Σ j·a_j`.

