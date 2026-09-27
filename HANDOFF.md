# VerticalStripLLT handoff

## Results and current task

The full ordinary AND circular flip-component HRV formulas now have complete
mathematical proofs. The ordinary word proof was audited by primary, Astra
and Terra at `2b9421e`. At the user's request we compared the new Overleaf v9
draft: primary and Astra independently accepted its bounded-face reduction
and exact whole-component coefficient invariance, which closes every circular
case. Terra checked the ordinary comparison and shorter HRV extraction.
Neither full component theorem has yet been formalized in Lean.

The user then asked for an easier-to-formalize argument without general
polyhedral machinery. A direct signed cycle-deletion recurrence now has an
independently audited longest-path toggle proof. Its canonical regrouping into
whole components still needs a direct finite proof. A finite gain-graph
coefficient statement isolates that task. This is a simplification and
formalization question, not a reopened gap in the complete v9 proof.
See [the comparison and circular proof](docs/proofs/COMPONENT_CIRCULAR_FACE_PROOF.md),
[component status](docs/FLIP_COMPONENT_STATUS.md), and
[Lean plan](docs/COMPONENT_FORMALIZATION.md).

The full ordinary and aggregate circular expansions remain Lean-verified.
The prior aggregate checkpoint `18fbb4d` passed 1908 build jobs and 2037
inventory checks using only `propext`, `Classical.choice` and `Quot.sound`.
The public circular declarations are
`coloringLLT_shifted_eq_eval_shiftedOrientationExpansion`,
`coloringLLT_shifted_eq_orientation_sum`, and `coloringLLT_shifted_e_positive`
in `VerticalStripLLT.Circular`. They cover all valid diagrams and alphabets.
The initialization commits `830cc6b`, `130f7e8` and immutable references remain
preserved. No shared Rust or Overleaf source was changed.

## Ownership and integrated Lean modules

Primary owns strategy, every current editable file, integration and the sole
global Lean build slot. Only primary uses `lake-workspace`; no transfer
occurred. Process checks found no competing batch build. Existing RealRooted
Lake serve/LSP processes were left untouched. All subagents released ownership;
no remote task or observer remains active.

The user authorized parallel Lean implementation. The modular plan and ownership
were committed at `683e4e7` before delegation. Luna returned two disjoint,
build-free candidates. Primary reviewed, repaired and locally verified them,
then committed and pushed `a8ebd20`:

- `Components/WordRelations.lean`: `WordModule`, `basisWord`, `fourWord`,
  `wordGenerators`, `wordRelations`, `WordQuotient`, `relations_le_ker`,
  `descend`, `descend_mk`, `quotient_eq_implies_eq`.
- `Components/WordContext.lean`: `contextLinear_basisWord`,
  `contextLinear_fourWord`, `contextLinear_relations_comap`,
  `contextLinear_map_relations`, `contextQuotient`, `contextQuotient_mk`.

Aristotle returned the isolated general-ring conjugation task. Primary ported
and integrated `Components/WordConjugation.lean` with narrow imports and `lia`:

- `descendingProduct_mul_inverseProduct`;
- `inverseProduct_mul_descendingProduct`;
- `descendingProduct_conj`;
- `letterSum_commute_descendingProduct`;
- `descendingProduct_conj_adPow`.

All paths are below `VerticalStripLLT/`; namespace
`VerticalStripLLT.Components`. The general algebraic hypotheses are explicit.
The word quotient is still additive: induced multiplication, the actual
component-count pairing, direct HRV extraction and full Cauchy factorization
remain to be implemented. These modules do not claim the component theorem.
Primary also owns the root imports, inventory and synchronized scope/status docs.

## Aristotle provenance and checks

Project `7e1e7b8f-b94d-4eef-86cf-51b2130269f5`, task
`44384423-1c84-42b4-a525-bba5b13212f3`, is terminal COMPLETE. Native observer
`50488` ended normally. The remote candidate used its coherent Lean 4.28.0
cache with primary permission; the integrated source was checked locally with
pinned Lean 4.34.0 / Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
No remote package configuration or toolchain was imported. Exact input/output
hashes and remote versions are in [the ledger](docs/ARISTOTLE.md).

The integrated library build passed (1912 jobs). The updated inventory audit
passed all 2059 entries with only the three standard axioms. Source guards,
100-column checks, 113 local links/anchors, unchanged Overleaf source hash,
initialization ancestors and whitespace checks passed. External logs and returned sources are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/word-conjugation/`:
`conjugation-build.log`, `conjugation-library-build.log`, and
`conjugation-axioms.log`. The earlier word-only checkpoint passed its library
and inventory checks; its logs use the `word-` prefix. No placeholders,
custom axioms or unchecked native proofs are permitted.

## Overleaf source and mathematical comparison

Read-only source:
`/home/paxinum/Dropbox/Apps/Overleaf/LLT flip/Circular Vertical-Strip LLT Polynomials-v9.tex`.
SHA-256 `3b02859804569cf17a9fc037bd69390fc1afae2265cff559c752369ef05c9195`.
The old `main.tex` retains incomplete recurrence sketches; it is not the v9
proof we accepted. The new circular argument belongs to the draft, not to
this repository's preceding proof search. No attribution to a particular
external agent was inferred from file timestamps.

V9's ordinary nested-commutator extraction is shorter than our mixed-poset
refinement. We will combine it with our finite strict/e factorization, avoiding
an unnecessary rational or infinite symmetric-function layer. Its circular
proof expands in bounded tight-edge graphs, preserves the actual lifted HRV
vector by box thresholds, and proves coefficient constancy by an involutive
flip of the ORIGINAL source component with exactly the same face.

The [periodic word audit](docs/proofs/COMPONENT_PERIODIC_WORDS.md) remains a
valid explanation of why the ordinary quotient cannot be copied unchanged.
Its negative-winding obstruction is no longer an unresolved theorem case.

## Exact next steps

Push this verified integration, then pursue two bounded tracks:

1. Ordinary Lean integration: concrete word multiplication, actual component
   permutation counts using existing circular flips under a forward-edge
   hypothesis, and the direct sink-cancellation HRV extractor from v9.
2. Simpler circular companion: prove the finite gain-graph coefficient
   expansion combinatorially. Cycle deletion already preserves both valuations
   and decreases edge count, but arbitrary termination does not prove
   whole-component terminal multiplicities. Do not claim confluence or a
   discrete matching without constructing it. The polyhedral proof remains
   the complete mathematical reference.

A filename/API search in pinned Mathlib found homological Euler characteristic
but no ready Brianchon--Gram/polyhedral Euler module. This motivates the finite
route; it does not establish that a smaller formalization is already complete.
The active goal has made substantial progress. Requested formalization and
simplification work remains; no blocking condition is present.
