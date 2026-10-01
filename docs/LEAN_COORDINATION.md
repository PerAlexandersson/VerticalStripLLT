# Lean coordination (Claude-owned)

Claude owns this file. It reports the state of the Lean diagram formalization
to the Codex writer, who incorporates it into `HANDOFF.md`. The ownership
transfer is recorded in `HANDOFF.md` at `b78312c`: Claude owns all
`DiagramProof/` Lean sources, `DiagramProofVerification.lean` and the sole
project build slot.

## Current status — 2026-10-01

### Verified: right-endpoint attachment (issue #8, the attachment subtask of P9)

This checkpoint is the attachment lemma only. It is **not** all of P9 and not
the completed formalization. Its inputs are the marked recurrence and the
semantics; no component-expansion theorem is assumed.

New modules, all in `VerticalStripLLT/Components/DiagramProof/`:

| Module | Content |
| --- | --- |
| `RightAttachmentDiagram` | Embeddings `attachLeft`/`attachRight` (shared vertex `p`); the generic `attachUnion`; the predicate `IsRightAttachment G L R`; restriction/`glue`/`stateEquiv` on actual orientations; the constructed union `attachDiagram` with exact strict corners (`attach_isCorner`); `isRightAttachment_induced` for a forward diagram with a cut at `p` |
| `RightAttachmentPaths` | Internal covers; `flip_glue_iff` (a flip of the union is one factor flip with the other fixed); `reachable_glue_iff`; `flipComponent_glue` (whole component = image of the product of the two whole components, both directions) |
| `RightAttachmentValues` | Endpoint-omitted values (`omittedRelationValue`, `omittedMarkedK/E`, component versions), defined as products over the other vertices; `hrv_glue_left`/`hrv_glue_right` (exact HRV merger) and `fibre_glue_valid`; `relationValue_attach` (fixed-colour gluing); the state and component K/E gluing formulas; boundary lemmas `omittedRelationValue_one` (one-vertex attachment) and `relationValue_zero_alphabet` |
| `RightAttachment` | `attach_transfer`: from right-marked K and E identities with one list `z : ι → ℤ` (via `•`) to the unmarked identities for `P*T`, `P_i*T`, together with whole-component identification; measures `naturalArea`, `areaMoment`, with `naturalArea_eq`, `areaMoment_eq`, `attach_measure_lt` |

Modelling decisions:

- Vertices are indexed by `Fin (p+1)`, `Fin (q+1)` and `Fin (p+q+1)`. Both
  `p = 0` and `q = 0` are covered by the general statements.
- `IsRightAttachment` is an edge correspondence, not an equality of
  diagrams. P9 can therefore apply it either to the source diagram's own
  induced sides or to constructed unions with varying prefixes.
- Marked values fix the colour at `Fin.last p`, the prefix's greatest
  vertex. The attachment's factor omits its minimum vertex `0`.
- No identity between `K(T)` and `E(T)` is assumed.

Checks:

- Focused `lake-workspace build` of `VerticalStripLLT.Components.DiagramProof.RightAttachment`
  passes, rebuilding the three dependent modules.
- `lake-workspace env lean DiagramProofVerification.lean` runs all 719
  axiom queries, 70 of them new. Every query uses only `propext`,
  `Classical.choice` and `Quot.sound`, or no axioms.
- The import closure of the verification file grew from 282 to 286 project
  files, exactly these four. It contains no word/scan, block-extractor or
  old component-expansion module.
- Source guards pass: no `sorry`, `admit`, `native_decide`, custom axioms or
  `omega`; all lines are at most 100 columns; no trailing whitespace.

Logs are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/claude-right-attachment/logs/`:
`attach-3.log`, `axioms-1.log` and `imports-1.txt`. Earlier logs contain
superseded repairs.

### Verified: P6 common-cover uniqueness without articulation

`CommonCoverUniqueness.lean` proves `commonCoverUnique_of_shortEdges`:
for every forward diagram with `ShortEdges D`, i.e. every natural edge of
length at most two (the no-articulation condition), connected common-cover
states of equal total size are joined by actual flips. It has no remaining
hypotheses. The proof is strong induction on the vertex count:

- base cases: at most two corner chains (`commonCover_connected_of_terminal_card_le_two`)
  and complete diagrams (`reachable_of_complete`, via `clique_reachable_of_block`
  with the identity core);
- second corner tail `1`: initial-vertex inheritance
  (`commonCover_connected_of_initialVertex_short`) on `Fin.succOrderEmb`;
- second corner tail `>1`: first-clique inheritance on `{0} ∪ [b, n-1]`, with
  the core embedding chosen as the reversal of `lastCliqueEmbed`. This makes
  `lastClique_induced_short_naturalEdges` apply after `reverseOrderEmbedding_involutive`.

All 724 axiom queries pass with only standard axioms (`axioms-2.log`).
The initial-path extension remains (next).

### Open questions for the writer

- **Coefficients.** The transfer uses `z i • V` with `z : ι → ℤ`. P8
  certificates should use the same form, or adapt to it with one lemma.
- **Measure.** `naturalArea = ∑ a_j` and `areaMoment = ∑ j·a_j`, taken from
  the diagram's own area sequence. The decrease is stated lexicographically
  on `(area, moment)` for prefixes on the same vertex set; the vertex count is
  then equal automatically.
- **The draft proof.** The Lean proof matches the written argument step by
  step: triangles lie on one side, covers are internal, a flip changes
  exactly one factor, and the fibres at `c` merge with `c` contributing one
  weight. No clarification is needed.

### Remaining obligations (unchanged goal)

- **P6.** The initial-path extension of common-cover uniqueness.
- **P7.** Smaller-component corrections and envelope normalization.
- **P8.** Right-marked full-layer NN/DN recurrences and component isolation.
- **P9, rest.** Articulation prefix selection, first-drop coverage, and
  using `attach_transfer` with the four contact cases.
- **P10.** Well-founded induction, weights, positivity and the final
  independent theorem.

Next Lean step: resume P6 from the `b78312c` interfaces, following
`HANDOFF.md`'s "Next obligations" and the plan.
