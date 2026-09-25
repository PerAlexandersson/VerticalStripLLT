# Aristotle proof-search ledger

Aristotle results are proof candidates. Primary owns submissions, monitoring,
downloads, integration, and local Lean 4.34 verification. Luna owns the assigned
implementation files. Keep generated requests/results outside the checkout.

## Strict-chain elementary identity

- Project ID: `262ce79f-3c8a-4e6a-83f7-6fcf6a6c9eb6`.
- Submitted 2026-09-25 through the installed `aristotle` CLI.
- Request directory:
  `/lake-cache/ai-projects/requests/VerticalStripLLT/strict-chain-esymm`.
- Exact target: for every `n m : ℕ`, the sum of `∏ i, x_(c i)` over strictly
  increasing functions `c : Fin n → Fin m` is
  `MvPolynomial.esymm (Fin m) (Polynomial ℤ) n`.
- All boundary cases are included. No LLT recurrence or expansion is assumed.
- Intended use: combine with the independently proved graph/coloring
  characterization of `n d^k e` to establish the manuscript's general base case.
- Suggested proof: finite subsets of cardinality `n` correspond to increasing
  enumerations via `Finset.orderEmbOfFin`.
- Environment warning: service reports Lean 4.28.0; local target is Lean 4.34.0,
  Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Port and verify locally.
- Task ID: `1ffc730d-dfb2-4d27-9d61-b0f0cc851e0f`.
- Its live event contained a complete candidate using `Finset.sum_bij` and
  `Finset.orderEmbOfFin_unique`. The event body is retained externally as
  `candidate-body.lean` in the request directory. An interim downloaded archive
  still contained the original placeholder, so this is explicitly event-based
  provenance, not a claimed completed service export.
- Luna ported that candidate to `VerticalStripLLT/ElementaryColorings.lean`.
  Primary's Lean 4.34 focused and full builds passed; the public axiom audit
  showed only standard Lean axioms. `ColumnBase.lean` combines the result with
  the graph characterization to prove the general column initial condition.
- After this exact proof was locally verified, primary canceled the redundant
  still-running service task to free capacity for multiplicativity. SDK status
  was explicitly re-read as `CANCELED`. This was not an observation timeout or
  a claim that the service completed its own run.

## Prepared concatenation request

- Request directory:
  `/lake-cache/ai-projects/requests/VerticalStripLLT/path-concat`.
- Contains the existing path model and six append/translation laws for path
  validity and the two edge scanners. No manuscript files or credentials.
- Submission was rejected because the service permits no additional project
  while the first task is running. There is no accepted second project ID.
- Do not resubmit until capacity is available and local task ownership has been
  reconciled; Luna may implement these elementary structural inductions locally.
- Superseded: Luna implemented these laws in `Concat.lean`, and primary fixed
  the last normalization steps and verified them. No remote submission needed.

## Coloring multiplicativity (completed and locally verified)

- Project ID: `0ae224b5-c423-4820-80fe-66635b0c8c93`.
- Task ID: `1f6544ca-c869-470a-8f4a-514afa8ca2a8`.
- SDK query confirmed `COMPLETE`, 100 percent, on 2026-09-25.
- Request directory:
  `/lake-cache/ai-projects/requests/VerticalStripLLT/coloring-concat`.
- Self-contained snapshot of the checked path, bounds, concat, polynomial, and
  coloring definitions; no private reference material or credentials uploaded.
- Exact target: `coloringLLT (P.concat Q) m = coloringLLT P m * coloringLLT Q m`
  for all valid paths and finite alphabets. The request includes the graph
  decomposition, coloring equivalence, ascent, and finite-sum proof outline.
- Completed export retained as `result.tar.gz`; selected source extracted as
  `completed-candidate.lean`. The diff preserves all existing definitions and
  statements, adds helper lemmas, and replaces the final proof placeholder.
- Luna ported its new declarations to `ColoringConcat.lean`. Primary repaired
  remaining Lean 4.34 simplifier transparency differences, verified focused
  and full builds, and audited the public theorems' axioms.
- The result proves the disjoint graph decomposition, admissibility and ascent
  factorization, pointwise weight multiplication, and `coloringLLT_concat`
  for every path pair and finite alphabet. The finite sum uses `Fin.appendEquiv`.
- The remote job changed its isolated toolchain to Lean 4.28 and used Mathlib
  v4.28.0. The local toolchain and manifest remain unchanged at Lean 4.34.

## General unicellular relation (active)

- Project ID: `7cac7db7-a2d1-4c27-8522-9b43c7690ed8`.
- Task ID: `2496607b-8e35-455c-9ee7-7a60c6ef4618`.
- SDK query confirmed `IN_PROGRESS` after submission.
- Request directory:
  `/lake-cache/ai-projects/requests/VerticalStripLLT/general-unicellular`.
- Self-contained snapshot of nine checked local modules, including path
  resolutions, the marked diagonal, and the pointwise edge-insertion weight
  identity. No reference material or credentials were uploaded.
- Exact target: for a valid `U d V`, prove
  `G_(U ne V) - G_(U en V) = C(q-1) * G_(U d V)` for every finite alphabet.
- Remaining proof outline: scanner insertion identities by induction on U,
  corresponding finset identities, freshness from strict/normal disjointness,
  then the checked pointwise identity and summation.
- This isolated request pins the observed service environment Lean/Mathlib
  v4.28.0, avoiding the earlier initial toolchain mismatch. All returned
  candidates must still pass the unchanged local Lean 4.34 environment.
- Observe this exact handle; do not duplicate a live task after an observation
  timeout. Luna should port its candidate; primary remains sole local builder.

The API credential is loaded by the shared environment helper and is never
passed on the command line or stored in this repository. Do not upload the
workspace or reference snapshot wholesale; requests contain only needed inputs.
