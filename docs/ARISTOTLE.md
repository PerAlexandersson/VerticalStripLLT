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

## Terminal-clique transfer repair — locally verified

- User explicitly requested Aristotle and subagents during the diagram
  formalization. Project `515b9f61-1e1a-43bf-99b7-9e05cbff2124`, task
  `84ef24e0-68a0-41fa-becb-c58e46b183d6`, terminal status **COMPLETE**.
- External directory:
  `/lake-cache/ai-projects/requests/VerticalStripLLT/terminal-transfer-repair/`.
  `TARGET.md` SHA-256:
  `d80bdec1409e50462ffbc1f3b4bca770afcc20fcca76244320af35ebe7803f3e`.
- Scope: the exact one-temporary-edge repair from the terminal-clique proof.
  Input is a connected simple graph, donor/receiver edges, and the Boolean
  telling whether a donor copy remains. Output is either the direct pair
  of connectivity conditions or an absent temporary edge satisfying both
  successive pairs. The request supplies the written bridge-cut proof.
- Returned `RequestProject/Repair.lean` proves the exact disjunction and even
  omits finiteness, with no extra hypotheses. The downloaded archive is
  `result.tar.gz`; extracted source and `ARISTOTLE_SUMMARY.md` remain in
  `terminal-transfer-repair_aristotle/` under the external directory.
  Terra ported it build-free to `DiagramProof/TerminalRepair.lean`; primary
  verified the focused build under local Lean 4.34.0. An independent
  read-only review approved the exact contract and both donor-copy cases.
- No scans or alternative LLT proof routes are requested. The remote may use
  its cached toolchain; returned source must be ported to local Lean 4.34.0
  and pass the serialized focused build, source/import and axiom guards.
  `TerminalRepair.one_temporary_edge_repair` is now locally proved, with
  only `propext`, `Classical.choice` and `Quot.sound`. The source uses the
  narrow connectivity import and no old LLT proof route. Verification logs:
  `diagram-formalization/p5-terminal-repair-build.log`, `p5-repair-axioms.log`
  and `p5-repair-imports.txt`. The direct diagram transfer and its application
  to capacities remain separate obligations; the graph lemma assumes no
  capacity model and needs no finiteness hypothesis.

## Circular finite coefficient identity: accepted mathematical proof

- Project `729ff94c-1911-422b-88a7-f1af1cef93d0`, task
  `91a37895-7b0f-420d-aa72-92da80540500`, terminal service status
  **COMPLETE_WITH_ERRORS**. Its mathematical response claims a complete prose
  proof. No Lean proof or enumeration was requested or returned. We accept
  the corrected mathematics on independent review, not on the service label.
- External directory `circular-finite-coefficients/` under the request cache.
  `TARGET.md`, SHA-256
  `0f82f88595fabe734ee15a4eb3cb15e9bfab60c6954a707d9a3db51769a02a6f`.
  `result.tar.gz`, SHA-256
  `0d5276fceb32611f70855d2a8120ba17015f54584d20d87f59002a6fb6505f11`.
  `returned-PROOF.md`, SHA-256
  `84e8fdf12b20c74ec923b3dbc8796a6acf39d8228f3cd8ebdea2e9b061ded327`.
- Primary and Astra independently checked all coefficient signs, contraction,
  ordered-partition cancellation, the scaled longest-path potential toggle,
  the balanced base and strict edge-count induction. Terra independently
  checked the ordered-partition identity and the two-case reindexing.
- Correction: the unused introductory assertion about unscaled INTEGER strict
  potentials is false. Negative gain cycles imply rational strict potentials,
  obtained by dividing the scaled integer construction by M. The returned
  proof's actual toggle uses the correct scaled construction. The corrected
  repository note removes the false declared input.
- Primary then wrote the complete finite component-isolation argument using
  identical contracted gain graphs and zero-slack lifted paths; Astra checked
  it independently, including the integer-period issue. It uses no faces,
  boundedness or Euler characteristic.
- Accepted result: [finite companion](proofs/COMPONENT_FINITE_COMPANION.md).
  This answers the user's simplification request for the complete circular
  theorem. The corrected companion was subsequently formalized and integrated
  into the full component theorem; see [the completion audit](COMPONENT_COMPLETION.md).
  No remote toolchain, package files or generated artifacts were imported.
- Observer sessions `71491` and `58068` had transient connection failures.
  Subsequent queries used the same task; no replacement task was started.
  All Aristotle tasks relevant to this batch are now terminal.

## Finite word conjugation: complete, locally integrated candidate

- Project `7e1e7b8f-b94d-4eef-86cf-51b2130269f5`, task
  `44384423-1c84-42b4-a525-bba5b13212f3`, terminal **COMPLETE**.
  Native observer session `50488` ended normally. No new task is queued.
- External directory `word-conjugation/` under the requests root. `TARGET.md`
  SHA-256 `33d7d0303f6b8637f62c9fbe23fca084fe9006b36436d4ed28b26b730e5d3512`.
  The request supplied the audited algebraic proof and prohibited scans.
- The remote cached environment was Lean 4.28.0 / Mathlib
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365`. Primary explicitly permitted
  its use for the candidate instead of rebuilding Mathlib. All local checks
  still use the project's pinned Lean 4.34.0 and Mathlib revision.
- Downloaded `result.tar.gz`, SHA-256
  `22dc0fa6372dc4475b0a983d1228d4d31fd9e3d5d34c1e45424aded338d91ea0`.
  Retained `returned-WordConjugation.lean`, SHA-256
  `d73c4482643aafe0d9e33d09af07c2cd50a08355ad7b4f3d1d3de87b738594f5`.
- Primary read the complete return, checked all hypotheses against TARGET,
  narrowed imports, ported arithmetic to `lia`, and integrated only
  `VerticalStripLLT/Components/WordConjugation.lean`. No remote package,
  manifest, toolchain or project configuration was imported.
- Completed declarations: `descendingProduct_mul_inverseProduct`,
  `inverseProduct_mul_descendingProduct`, `descendingProduct_conj`,
  `letterSum_commute_descendingProduct`, and `descendingProduct_conj_adPow`.
  The focused local build passed on 4.34.0. The library/inventory integration
  checks are recorded in HANDOFF. These prove the requested general algebraic
  lemmas, not either full component theorem.
- Luna separately supplied the additive word quotient and contextual stability;
  primary integrated those at `a8ebd20`. All local builds were serialized.

## Mixed-corner residual: completed partial result

- Project `3fd0ed1d-ba60-404b-8b99-beaaae1c4d08`; new task
  `4aa8cbee-7eb5-4d15-ba07-7806c7fa540a`, terminal **COMPLETE**. Its return
  explicitly does NOT prove the residual identity or a uniform recurrence.
  The preceding task was confirmed terminal before this submission.
- External directory `mixed-corner-residual/` under
  `/lake-cache/ai-projects/requests/VerticalStripLLT/`.
- Four uploaded files: TARGET and snapshots of COMPONENT_CORNER_DIFFERENCES,
  DN_COMPONENT_COMPLETION and FLIP_COMPONENT_INDUCTION from `4aa6667`.
  `INPUT_HASHES.json` records all exact snapshot hashes.
- `TARGET.md` SHA-256
  `428caaf494e5330672feae662aa28d0ae924aee78fd4a51b5b74843af95a867d`.
  The request supplies the proved ordinary corner quotient, signed recurrence,
  mixed-cycle involution and explicit HRV-map coefficient formula as INPUT.
  It asks for the remaining whole-component residual identity or an actual
  uniform component recurrence, and forbids broad scans or conditional scaffolds.
- Further input `MAP_COEFFICIENT_ADDENDUM.md`, SHA-256
  `ba19d573fcfe2151da8878d5b3c78db9b156530c430174ccf77f47e0ad68fcca`.
  It supplies the audited signed count at a fixed map and the exact failure
  of vertex-color-preserving canonical-chain matching. These are local results,
  not outputs attributed to the remote service.
- Uploading the addendum as a file was rejected because the task was already
  running. Sending the same text inline was accepted; see
  `addendum-submission.log` and `addendum-inline.log`. `aristotle tasks`
  subsequently confirmed the SAME running task ID. No retry task was requested.
- A further accepted inline reminder, `geometry-reminder.log`, emphasizes that
  strict edges must be actual natural corners. Shorts of a deleted long are
  generally not valid strict decorations; their derivatives need independent
  reconstruction before induction.
- The remote started an n=7 `run3.py` scan despite the explicit no-scan scope.
  Primary sent `stop-scan-request.log`, requesting termination of that scan
  while preserving the proof task. The final return reports that the scan had
  timed out and no enumeration process remains. Other remote scans also appear
  in the event receipt; none was requested or is used as proof. The return's
  wording about later scope narrowing does not change the initial no-scan scope.
- Native observers `83731` and `72078` both ended after stream interruptions;
  direct SDK reads of the SAME task confirmed its continuing work and later
  terminal status. No replacement proof task was started after either interruption.
- Downloaded `final-result.tar.gz`, SHA-256
  `a16c65204cea06dccccc50cb36427451a4708f6438a0a9db175d4e375de4eeef`.
  Extracted `final-RESIDUAL_BRIDGE-0.md`, SHA-256
  `a1d29ed66bcd37e02a3e15297f0e8d69d61e48ba1eda392527014bf86b19f6d5`.
  Primary read the full return. No returned source or experiment implementation
  was imported.
- Accepted after audit: the two residual diamond identities and the exact
  obstruction to regrouping weighted corner-long pairs in the known K4 tree
  component. The [owned HRV note](proofs/COMPONENT_HRV_DIFFERENCES.md#residual-diamonds-and-a-reconstruction-obstruction)
  records the formulas, valid smaller diagram and explicit contradiction
  t=0=1−t. The return's recurrence criterion is conditional, not uniform.
  Normal-long diamonds have a higher-normal-level term, so the proposed
  level induction does not automatically handle them.
- The new [chain normalization](proofs/COMPONENT_CHAIN_NORMALIZATION.md) came
  from primary, Astra and Terra work during this consultation. It was not part
  of the uploaded input or the remote return. Its fibers need further semantic
  regrouping, and no full component theorem is claimed.
- No remote Lean source or local build was produced by this consultation.

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

## Auxiliary Claude DN consultation: no new proof

- Read-only Sonnet consultation, native session `90205`, terminal exit 0 in
  about five minutes under a monitored 20-minute cap. No tools, MCP servers,
  edits or builds were delegated. No consultation remains active.
- External directory `claude-dn-completion/` under the requests root above.
- `PROMPT.md`, SHA-256
  `4764570da8ce345d9ae22c12b1be9b1c894ac2f704fa26aa8ac79e3b447e88b7`.
- `response.json`, SHA-256
  `f3a4f98afd81527b7b7997a9d2517e8a0c638c20487939c6559c34b17c2e183a`.
  The response explicitly leaves general packet generation open. It restates
  the existing multiwindow row-span criterion; no new proof was accepted.
- Primary audit: membership in the same class for EVERY window is the
  intersection of those equivalence relations, not connectivity in the union
  of their graphs. Pairwise distinct incidence columns do not imply full
  rank: partitions {12},{34} and {13},{24} distinguish all four columns but
  have kernel (1,−1,−1,1). The global articulation counterexample to
  total-ascent uniqueness does not establish failure of any DN window.
  Activity at two corners does not supply two eligible DN instances; their
  contact, gap and equal-area hypotheses must still hold. Rational row span
  with denominator clearing suffices; integer row span is unnecessarily strong.
- The new alternating-deletion and mixed-cycle companions in
  [corner differences](proofs/COMPONENT_CORNER_DIFFERENCES.md) came from primary,
  Astra and Terra work, not this Claude return. They are audited prose and
  have not been ported to Lean. They do not finish the component theorem.
