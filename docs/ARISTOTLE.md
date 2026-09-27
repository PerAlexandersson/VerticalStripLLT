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

## Component recurrence: explicit DN redistribution and boundary residual

- Project `3fd0ed1d-ba60-404b-8b99-beaaae1c4d08`, new task
  `16154bfd-ae04-49cd-9549-6d0a931f9309`; accepted and initially **QUEUED**.
  Current monitoring state belongs in HANDOFF.
- External directory `component-recurrence/` under the requests root.
  `TARGET.md` SHA-256
  `2e9d4112c0a6fdcb7702c84db0a7bb990bbd427582ec21f3786dc5d233ccc54a`.
  `INPUT_HASHES.json` records exact source snapshots. The five uploaded files
  were TARGET, FLIP_COMPONENT_INDUCTION, Flip.lean, DNOrientationBlocks.lean
  and SecondBounceOrientation.lean. CIRCULAR_FLIPS.md was snapshotted but not
  uploaded; the accepted prompt states this omission.
- The first submission was rejected before task creation for exceeding the
  five-file limit. The five-file retry was accepted; there is only one new
  task. Logs are `submission.log` and `submission-retry.log`.
- Primary supplies the exact DN exterior maps, signed multiplicities with
  free parameter β, independently reviewed nonflip classification, ordinary
  deletion quotient, cover-boundary defect equation and its lower-area
  residual. These are inputs, not results of the new consultation.
- The request replaces AU_prime as the main target and asks for the actual
  global reconstruction into whole smaller components. It explicitly forbids
  assuming local packets are complete, pointwise middle-state HRV matching,
  or discarding the deletion residual. No return or full proof is claimed.
- Primary subsequently supplied `POTENTIAL_ADDENDUM.md` inline, SHA-256
  `bb5a20333d5ed174e948e5a5e5205be87926b2f68a93a782f8d6101f69824c32`.
  The parity change γ(Q)=(-1)^|Q|β(Q) makes reconstruction equivalent to
  vanishing of all closed-walk periods on the exterior-subset multigraph.
  Astra and Luna independently checked the criterion; actual period vanishing
  remains requested. The addendum was accepted into the SAME running task,
  confirmed by the unchanged task ID. Its log is
  `potential-addendum-submission.log`; no second task was created.
- Further inline inputs to the same task record the next audit, all external:
  `EXACT_CERTIFICATE_REQUEST.md`, SHA-256
  `a24b2a0de0d45ccac2c527b637945abc53d8e987bb0aaccacec6524161ef05af`;
  `CANONICAL_RESIDUAL_AUDIT.md`, SHA-256
  `ebac55b53f5efa874d536cf91cefffea98770495c6f9aeeba14738367567123a`;
  `SHARED_CORNER_SPACE.md`, SHA-256
  `c5393ca9c436c40eaefa63fdb7cb2476e42bf0cdb143eab0f89692faebccec69`.
  Primary asks for an exact certificate of a streamed computational failure,
  supplies the audited ordinary residual and its explicit two-edge obstruction,
  and supplies the common lower-diagram component sectors. These are user-side
  proof inputs/audits, not evidence that Aristotle completed the full goal.
  The task was still IN_PROGRESS when the observers disconnected. Primary
  requested finalization of the partial consultation and termination of its
  unwanted n=7 scan in `finalize-request.log`. No replacement task was started.
- Final authoritative status: **COMPLETE**. The return explicitly leaves
  the ordinary and circular component theorems unproved. It reports that
  the n=7 scan was terminated with no result. Both native observers are
  finished; completion was confirmed by `aristotle tasks` and `show` for the
  exact task ID.
- Downloaded `final-result.tar.gz`, SHA-256
  `4e0280ef1517181df47a275f20665fd23dd37168f20c02bf8c465d7ed3d06e96`.
  Extracted `final-PROOF.md`, SHA-256
  `6144dad9643f5cf620410a7e7b50a297a859a4e59caf5af4513f88228c8d7fa0`.
  Primary read the complete proof return. No returned Lean or experiment
  implementation was imported.
- The result audits the supplied DN geometry, endpoint maps, canonical
  residual and inactive-corner deletion. Its DN-T condition asks for an
  integer combination of whole inactive components which cancels the
  nonflip residual and reconstructs the target. Existence remains open.
  Remote n≤6 solvability was checked over the rationals, with integrality
  not systematically verified. These counts are remote evidence, not proof.
- Primary independently checked its five-vertex corrected packet using the
  existing model: adding the inactive two-state component produces target
  coefficients +1,+1,−1 on the three listed ENTIRE components. Receipt:
  `remote_certificate_audit.json`. This refines the already-proved diagnostic
  identity; it is not a new general theorem.
- Audit corrections: Corollary 3.2 needs source multiplicities constant on
  actual flip components, as in the owned note; it does not hold for arbitrary
  multiplicities. The claimed cover witness `abd` in §6 is redundant; `abc`
  is a valid witness. Its final `h` expressions use the weak convention and
  must become `e` in its stated strict convention. Lemma 4.1(b) requires its
  explicit support-on-redundant-states hypothesis, omitted in the summary.
- Primary's subsequent [explicit completion graph](proofs/DN_COMPONENT_COMPLETION.md)
  strengthens the conditional reconstruction to a concrete sufficient grouping
  rule and supplies the ordinary lexicographic measure. Terra audited this
  proof. Isolation of the active component within each group is still open;
  neither the remote return nor the finite fixtures establishes it.

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

## Auxiliary Claude corner consultation: partial result, no AU_prime proof

- Read-only Sonnet invocation, native session `57970`, completed with exit 0
  within its 20-minute allowance. No tools, MCP servers or source access were
  delegated. Primary monitored the process. No restart followed its return.
- External directory `claude-active-corner/` under the requests root above.
- `PROMPT.md`, SHA-256
  `095fb5152cc23b7261bc0e97276e9bad82e0923f107cc3dee043f7d064419528`.
- `response.json`, SHA-256
  `f0033fce4e6dcee0e0f737a5bae28d69d34637795e5c1fd5e1f20b04edd084d5`.
  The response envelope reports success; its mathematical verdict explicitly
  leaves AU_prime unproved. Empty stderr is retained. An earlier invalid
  empty MCP configuration failed before the model task started.
- Valid result: for the saturated distance-two band graph, actual flips are
  adjacent 10↔01 swaps, so each ascent gives one entire component. Primary
  checked this and applied the aggregate theorem to obtain that full family's
  component HRV formula. See [the corner note](proofs/COMPONENT_ACTIVE_CORNERS.md).
- Rejected bootstrap: deleting a long strict corner creates unmarked corners;
  saturating them changes the state set. The suggested region where the
  deleted corner is redundant need not be a union of full components. The
  owned corner note gives an exact two-state counterexample. No part of the
  existing strict-corner quotient proof is replaced by this proposal.
- No Lean source or builds were produced. The response neither proves the
  ordinary nor the circular general component formula.
