# Lean coordination (Claude-owned)

Claude owns this file. It reports the state of the Lean diagram formalization
to the Codex writer, who incorporates it into `HANDOFF.md`. The ownership
transfer is recorded in `HANDOFF.md` at `b78312c`: Claude owns all
`DiagramProof/` Lean sources, `DiagramProofVerification.lean` and the sole
project build slot.

## Current status — 2026-10-01: the ordinary theorem is formalized by diagrams

The independent diagram-route theorem is proved in Lean:

```lean
theorem VerticalStripLLT.Circular.component_strict_eq_elementary_of_forward_by_diagrams
    {n : ℕ} {D : Diagram n} (θ : Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) (m : ℕ) :
    componentStrictEnumerator D θ m = evalElementary m (componentHRV D θ)
```

Its consequences, in `DiagramProof/Consequences.lean`, are:

- `component_weighted_strict_eq_eval_of_forward_by_diagrams`: restores the
  common shifted weight;
- `component_weighted_e_positive_of_forward_by_diagrams`: gives a homogeneous
  elementary-positive expansion.

These are statements about the existing semantics: the strict-coloring
enumerator and the evaluated HRV elementary monomials of every whole flip
component of every forward diagram, for every finite alphabet. They carry no
extra hypotheses.

Checks at `f2f396f`:

- Every new module passes a focused `lake-workspace` build.
- `lake-workspace env lean DiagramProofVerification.lean` runs **856** axiom
  queries. Each uses only `propext`, `Classical.choice` and `Quot.sound`, or
  no axioms (`axioms-3.log`).
- The import closure of the verification entry point has **313** project
  files. It contains no word/scan, block-extractor, `ComponentScalars`,
  `ComponentCoefficient`, `OrdinaryComponentExpansion`, `ComponentExpansion`
  or `CircularFromOrdinaryComponents` module (`imports-final.txt`).
  The earlier word-functional theorem is therefore not an input.
- Source guards pass for all 237 `DiagramProof` modules and the verification
  file: no `sorry`, `admit`, `native_decide`, `omega` or custom axioms; at
  most 100 columns; no trailing whitespace.
- Umbrella integration: `Consequences` is exported through
  `VerticalStripLLT.lean`. The full `lake-workspace build VerticalStripLLT`
  passes (2364 jobs, `full-build-2.log`). The existing `Verification.lean`
  audit, with the three new public theorems added, runs 2810 queries, all using
  only the standard three axioms or none (`verification-1.log`).
- Pre-existing break fixed: `Components/CompatibleDiagramSemantics.lean` lost
  its transitive `Circular.ComponentSemantics` import at `9d8c4bc`, when the P0
  extraction changed `SelectedColoringTransport`'s imports. No full build had
  run since. The module now imports `ComponentSemantics` directly; no
  declaration changed.

Logs are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/claude-right-attachment/logs/`.

## Module map and correspondence with the written proof

All modules are in `VerticalStripLLT/Components/DiagramProof/`.

### Shared foundation (streamlining)

| Module | Content | Written step |
| --- | --- | --- |
| `NaturalRelations` | `naturalRel`, `strictRel`; strict pairs are maximal (`strictRel_maximal`); orientations are determined by selected relations; states from valid relations | the relational model of ordinary diagrams |
| `RelationalTransport` | `directedFlip_iff`: a flip is exactly a short exchange under two covers. `Corresponds π θ θ'` transports flips, paths and whole components between any two forward diagrams along a vertex bijection that is order-preserving in selected weak blocks | "a maximal natural edge is never an exchanged short"; all identity re-presentations |
| `RelationalValues` | marked K/E are preserved by correspondences fixing the marked vertex | marked identities (EA1)/(RE1) under relabelling |
| `RelationalDiagram` | `ofRelations N S`: an ordinary diagram from an interval-closed natural relation and maximal strict pairs | every diagram operation (deletion, marking, reordering, targets) |
| `DiagramMeasure` | `naturalArea = #natural pairs`, `areaMoment = Σ heads`, `MeasureLT` | the order `(n, A, M)` |
| `Certificates` | `Cert k = Comp k →₀ ℤ` (integer combinations of whole components), right-marked `K/E` and unmarked `KU/EU` valuations, `Certifies`, `UCertifies`, component representatives of flip-closed sets | "the same signed list of whole components for K and E" |

### P6: uniqueness

| Module | Main result | Written step |
| --- | --- | --- |
| `CommonCoverUniqueness` | `commonCoverUnique_of_shortEdges` | common-cover uniqueness without articulation (vertex-count induction: two-chain and complete bases, initial-vertex and first-clique branches) |
| `InitialPathUniqueness` | `commonCoverUnique_of_initialPathBlock` | "an initial path can be added": pendant deletion as a path argument only |

### P7: corrections without a witness

| Module | Main result | Written step |
| --- | --- | --- |
| `AlternatingDeletion`, `AlternatingCertificate` | `certifies_alternating` | alternating deletion of strict corners; images are unions of whole components; cancellation at a redundant corner |
| `CornerCorrections` | `certifies_absentCorner`, `exists_saturate`, `certifies_noCommonCover` | absent-corner deletion; marking all selected maximal corners first |
| `BlockReordering` | `certifies_disconnected` | weak blocks placed consecutively, the greatest vertex's block last |
| `ComponentCorrections` | `certifies_of_not_hasCommonWitness` | the three direct corrections |

### P8: full-layer recurrences and isolation

| Module | Main result | Written step |
| --- | --- | --- |
| `LayerStates`, `LocalSplit` | layer sums over normal subsets; the split at two local shorts; `stateOf_diamond`; relabelling exterior selections | the local split `L_ij(Q)` |
| `NNRecurrence` | `NNContact.layer`: `X(L_(s+1)) = X(R_(s+1)) + X(R_s)` | NN on full layers: diamond, bottom swap, top closure |
| `DNRecurrence` | `DNContact.layer`: `X(L_s) = X(R_s)`; area kept, moment down by `t - y` | forward DN on full layers |
| `ComponentIsolation` | `certifies_of_layer`, `certifies_nn`, `certifies_dn` | (A2): isolate the unique witness component |

### P9: first drop, prefix and attachment

| Module | Main result | Written step |
| --- | --- | --- |
| `FirstDrop` | `exists_firstDrop`, `certifies_firstDrop` | the first-drop lemma; ND/DD reduce to NN/DN by unmarking the corner at `y` |
| `RightAttachment*` (issue #8) | `attach_transfer`, `attach_measure_lt` | the attachment lemma (A3)–(A4) |
| `AttachmentWitness` | the left restriction keeps saturation and a connected common-cover witness | P is connected with a witness |
| `PrefixAttachment` | `exists_prefix`, `uCertifies_of_witness` | the area-sequence prefix and the glued certificate (7) |

### P10: induction and consequences

| Module | Main result | Written step |
| --- | --- | --- |
| `DisjointUnion` | `IsDisjointUnion`, product components, `componentStrictEnumerator_glue`, `evalElementary_componentHRV_glue` | disjoint natural components factor |
| `Expansion` | `component_eq_by_diagrams_aux`, path base `component_eq_of_path` | strong induction on `(n, A, M)` |
| `Consequences` | the three public theorems | weights and positivity |

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

## Remaining items (optional; not needed for the stated theorem)

- The circular theorem is not re-derived by diagrams.
  `CircularFromOrdinaryComponents` imports word-route modules
  (`BlockCancellation`, `BlockExtractor`, `ComponentCoefficient`), so it was not
  used.
- Possible cleanups:
  - `attachDiagram` could be rebuilt on `ofRelations`;
  - `naturalRel` duplicates `CornerFamily.naturalEdgeRelation` (they are
    definitionally equal);
  - the NN and DN contact lemmas share swap/exterior arguments that could be
    factored further.
