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

## Coloring multiplicativity (active)

- Project ID: `0ae224b5-c423-4820-80fe-66635b0c8c93`.
- Task ID: `1f6544ca-c869-470a-8f4a-514afa8ca2a8`.
- SDK query confirmed `IN_PROGRESS` after submission.
- Request directory:
  `/lake-cache/ai-projects/requests/VerticalStripLLT/coloring-concat`.
- Self-contained snapshot of the checked path, bounds, concat, polynomial, and
  coloring definitions; no private reference material or credentials uploaded.
- Exact target: `coloringLLT (P.concat Q) m = coloringLLT P m * coloringLLT Q m`
  for all valid paths and finite alphabets. The request includes the graph
  decomposition, coloring equivalence, ascent, and finite-sum proof outline.
- Same service/local toolchain difference applies. Use current SDK status and
  this exact handle on continuation; do not restart because an observer expired.

The API credential is loaded by the shared environment helper and is never
passed on the command line or stored in this repository. Do not upload the
workspace or reference snapshot wholesale; requests contain only needed inputs.
