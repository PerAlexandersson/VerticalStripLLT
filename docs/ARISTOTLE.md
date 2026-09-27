# Aristotle proof-search ledger

Primary owns requests, monitoring, downloads, integration and authoritative
local Lean verification. Mathematical returns are proof candidates until
reviewed; a service completion status does not imply the requested theorem
was proved. Generated artifacts remain outside the repository.

[The archived ledger](archive/aristotle-ledger-through-endpoint-recovery.md)
preserves all earlier payloads, hashes, status transitions and integrated
ordinary/circular candidates. The entries below give current final outcomes
for the component search. [HANDOFF](../HANDOFF.md) owns running-process status;
[the proof map](FLIP_COMPONENT_STATUS.md) owns the mathematical overview.

## Ordinary corner refinement: complete return, AU_prime still open

- Project `3fd0ed1d-ba60-404b-8b99-beaaae1c4d08`.
- Task `c2a21316-805d-489f-a1c7-40f51b40b57c`: terminal **COMPLETE**.
- External directory: `projected-source-companion/` under
  `/lake-cache/ai-projects/requests/VerticalStripLLT/`.
- Input `ORDINARY_ACTIVE_TARGET.md`, SHA-256
  `82a8d82f1b37e1d8c7472f6f95abce6084599a744c78d73ce0600ef827a24cab`.
  The initial target was total-ascent active uniqueness (AU). Primary found
  the n=7 articulation counterexample and withdrew that target in the same
  running task, requesting an audit and refinement by block ascent counts.
- Primary subsequently supplied the strict-chain endpoint recovery and
  multivariate aggregate gluing proof inline. The return audits this input;
  it does not originate the endpoint argument.
- Downloaded `ordinary-active-final.tar.gz`, SHA-256
  `216746d65c8f587d63e0a5d899c5fa1314a0488e2be5d8bb27aff4a16fb789e6`.
- Extracted `ordinary-active-final-PROOF.md`, SHA-256
  `3eee0939e3ae41e9242464e105ecf12bed66b32c33b39663e239b1d06478df0a`.
  The archive prefix is `output-final_aristotle/`. Primary read the return.
- Sections 3–4 supply the general corner leaf lemma and connectivity of all
  ordinary spanning trees with a fixed envelope. Primary and independent
  Astra audited them. The owned proof is
  [tree connectivity](proofs/COMPONENT_TREE_CONNECTIVITY.md).
- The refined uniqueness statement AU_prime beyond trees is explicitly
  unproved. The proposed dense anchoring lemma is also unproved. Neither
  target nor the full component formula is claimed as solved.
- Audit corrections: state tree connectivity for any two such trees (a
  disconnected envelope has none). For forests retain each weak block's own
  envelope. In the endpoint audit, a triangular matrix with nonzero polynomial
  diagonal is injective, not necessarily invertible over that ring; use the
  recorded monomial cancellation. The one-vertex coincident-mark case is
  handled separately in the owned endpoint note.
- The same-task observer `38474` exited successfully. No remote Lean source
  was integrated and no local build was needed for these prose proofs.

## Projected-cover source companion: target unproved

- Same project, preceding task `e8b27b28-541c-4e91-a846-d4b0db50a739`:
  **COMPLETE_WITH_ERRORS**.
- Input `TARGET.md`, SHA-256
  `add2d23d98721710fa5d28df922f4d6f3a4088a18e35ba086e68fba7a780338c`.
  Requested StrongSrc for entire projected-cover components; the balanced
  reduction was supplied inline after review.
- `final-result.tar.gz`, SHA-256
  `c314e8834db81ca87f660cf329f56f09e83733347e63d7e3c773d8048f9cad0e`.
- `final-PROOF.md`, SHA-256
  `463e1cd13f3b6d132ef33745f1775f2f957a0586e91ffe6eaf840277a8a517b8`.
- Neither StrongSrc nor its first-order part was proved. Its partial tree
  argument is superseded by the later general tree proof above. No source
  candidate or compatibility scaffold was integrated. Same-task observer
  `31446` is historical; it is not a live proof task.

## Initial source companion: target unproved

- Project `d4b3ddfe-0051-4f80-b222-4e9374badcb3`, last task
  `ae0d9a91-dc02-4f53-97a9-3ed6f8034bcf`: **COMPLETE_WITH_ERRORS**.
- Primary and Astra checked useful conditional source/coefficient reductions.
  They do not establish the missing full cancellation. Earlier task
  `e8ff79a8-7d41-4d95-98ea-34cd691a4653` was deliberately canceled; it must
  not be reported as completed. Exact history and payloads are in the archive.
- No generated compatibility patches were imported. The source and sink notes
  retain the useful arguments and counterexamples.

## Completed aggregate formalization

The ordinary and full circular expansions are locally verified. Their final
scope is recorded in [ordinary completion](COMPLETION.md) and
[circular completion](CIRCULAR_COMPLETION.md). Earlier incomplete aggregate
Aristotle returns in the archive describe historical gaps, all subsequently
resolved by the local formalization. They are not current outstanding work.
