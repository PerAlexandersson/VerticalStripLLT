# Aristotle proof-search ledger

Aristotle results are proof candidates. Primary owns submissions, monitoring,
downloads, integration, and local Lean 4.34 verification. Luna owns the assigned
implementation files. Keep generated requests/results outside the checkout.

## Circular coloring subset expansion (completed and locally verified)

- Project ID: `40998e1f-04ed-473c-9d58-5656253cfa9d`.
- Submitted 2026-09-26 through the installed CLI; primary owns monitoring.
- Request directory:
  `/lake-cache/ai-projects/requests/VerticalStripLLT/circular-subset-expansion`.
- Exact target: `finite_subset_coloring_expansion`, the commutative-semiring
  identity expanding finite coloring ascent factors into edge subsets.
  `docs/CIRCULAR_GOALS.md` records the statement and its semantic use.
- No manuscript/reference material or credentials are included. The request
  contains only the standalone target, proof outline, and isolated v4.28
  environment. Local integration still requires the pinned v4.34 check.
- Task `a9e608b9-2049-4c1c-a62e-26a550d317c8` completed. Export retained as
  `result.tar.gz` and `completed-candidate.lean`; statement unchanged. Terra
  ported it to `Circular/SubsetExpansion.lean`. Primary verified this port
  and the generic selected-orientation semantic corollary locally.

## Circular acyclic walk bound (completed and locally verified)

- Project ID: `8da2f9e8-2c92-4aaa-83a7-a88f6f36d257`.
- Task `bdd5052c-9aeb-45f2-b951-0455c14d11d6` completed 2026-09-26.
  Luna ported `completed-candidate.lean` to `Circular/WalkBound.lean`; primary
  checked the unchanged statements and proofs with the pinned local toolchain.
- Request directory:
  `/lake-cache/ai-projects/requests/VerticalStripLLT/circular-walk-bound`.
- Exact targets: `acyclic_walk_injective`, `acyclic_walk_length_lt`, and
  `acyclic_lifted_walk_span_le`, for a finite acyclic relation on `Fin n` and
  an indexed walk. The last statement assumes each lift increment is at most
  n−1 and concludes displacement at most (n−1)², allowing multiple cut crossings.
- This standalone request contains no manuscript or assumed HRV result.
  Isolated service environment v4.28; all candidates need local v4.34 checks.

## Circular projected reachability bound (locally verified candidate)

- Project `e0fb05e6-3945-4336-a5a2-12db81eee4c5`, submitted 2026-09-26.
- Request directory:
  `/lake-cache/ai-projects/requests/VerticalStripLLT/circular-reachability-bound`.
- Exact target `projected_reachable_bounds`: every reflexive-transitive path
  in an integer relation projecting to a finite acyclic graph, with positive
  step increments at most n−1, has nonnegative displacement at most (n−1)².
- Includes the locally checked walk lemmas as a fixed prefix. This bridges
  actual reachability to the finite maximum used by circular HRV. Primary
  integrated `Circular/ReachabilityBound.lean` and verified it locally.
- Task `426c2208-87a1-4f9e-85eb-ff5c20fe0f70` returned
  `COMPLETE_WITH_ERRORS`: the supplied request had a duplicated namespace
  closing line. The candidate reopened the intended namespace, preserving
  the walk prefix and mathematical target. The extracted proof passes the
  authoritative local build and axiom check. Do not describe the service
  status as `COMPLETE`.

## Full circular elementary expansion (continuation returned without proof)

- Project `5835802e-8139-48b7-a07b-06add00f1f14`, task
  `f726d73c-794d-4693-8a20-58660dab3545`, submitted 2026-09-26.
- Request directory:
  `/lake-cache/ai-projects/requests/VerticalStripLLT/circular-expansion`.
- Target: `Circular.coloringLLT_shifted_eq_eval_shiftedOrientationExpansion`
  for every valid circular diagram and every finite alphabet, with no
  recurrence, no-wrap, or HRV equality assumption. Exact statement retained
  in `Target.txt` and `docs/CIRCULAR_GOALS.md`.
- The checked prefix includes direct coloring semantics, acyclic orientations,
  actual integer-cover HRV with greatest-reachability and lift independence,
  and the general selected-order expansion. No examples or manuscript files
  were uploaded. `INPUT_MODULES.txt` records the source modules.
- Isolated environment remains v4.28. Proof-only `ite_eq_right`/`ite_true`
  names were translated to `if_neg`/`if_true`, and a local elaboration option
  was omitted. The definitions and theorem targets retain their semantics;
  returned work still requires local v4.34 integration and verification.
- Primary first sent INSTRUCT steering away from rebuilding the proved zero-area
  family. After the task continued duplicate base work, primary downloaded
  `corner-checkpoint.lean` and canceled task `f726d73c-794d-4693-8a20-58660dab3545`.
  Cancellation is confirmed; it is neither completion nor a failed proof.
- The saved candidate contains one unproved `expansion_of_allCornersStrict`
  helper. That helper and its final unconditioned alias were not imported.
  Primary and Luna/Terra ported the useful corner geometry, coloring recurrence,
  orientation bijections, and HRV transport into seven small modules.
- `expansion_of_cornerReduction` instead exposes that missing helper as an
  explicit hypothesis. The squared-edge-count termination proof is checked
  locally. `expansion_of_strictCorners_positive` further removes the already
  proved zero-normal and strict-cycle cases. Terra independently audited the
  source correspondence and absence of circular reasoning.
- `Continuation.lean` and `CONTINUATION_INPUT_MODULES.txt` include complete
  local zero-normal proofs, strict-cycle vanishing, and corner reductions.
  AXLE preflight `3ddb3baa-97b2-4d60-9524-0b3c03cde99f` on `lean-4.28.0`
  reports no errors and only the intended remaining target as incomplete.
  This is a prefix compatibility check, not a proof of the target.
- Flattening renamed a colliding private helper and translated the RTC.lift
  endpoint convention and `dite_eq_left` name for v4.28. No definitions or
  mathematical statements were changed. Original `INPUT_MODULES.txt` is retained.
- Primary submitted the continuation to the same project with
  `CONTINUATION_PROMPT.md`, prohibiting duplicate bases, examples, circular
  assumptions, and a final theorem depending on an unproved helper.
- Continuation task `b6cda868-d1f9-4ec9-a51c-f81bff3c6354` returned
  `COMPLETE_WITH_ERRORS`. Primary downloaded `continuation-result.tar.gz` and
  retained `returned-Continuation.lean` and `returned-CONTINUATION_REPORT.md`.
  The target is still unproved; no new theorem was integrated. The original
  task remains `CANCELED`, and no continuation is active.
- The report lists circular bounce identities and termination as outstanding.
  Its discussion of missing ordinary proofs reflects the isolated payload;
  the full ordinary theorem is already checked in this repository. Reuse that
  implementation when preparing narrower tasks. Numerical exploration in the
  report was not imported or accepted as proof.

The author subsequently emphasized the existing draft recurrences as the intended
route. Primary sent their exact positive forms, the primary non-strict-area
measure, proposed secondary J rank, and periodic exterior-incidence mechanism
by INSTRUCT to the same running continuation. The message is retained as
`RELATIONS_STEERING.md`; it preserves the theorem target and all definitions.

## Circular zero-area expansion (capacity rejection; now proved locally)

- Request directory:
  `/lake-cache/ai-projects/requests/VerticalStripLLT/circular-zero-area`.
- Exact target `coloringLLT_shifted_eq_expansion_of_no_normal`: the full
  arbitrary-size zero non-strict area family, for every finite alphabet.
- Prefix includes the checked general HRV foundations, zero-area edge bounds,
  strict-cycle vanishing, HRV roots, and the general strict-chain enumerator.
- Submission on 2026-09-26 was rejected by the service's concurrent-project
  limit. No project or task was created. At rejection, the main full-expansion request
  was active; no task was canceled to submit this.
- This family was subsequently proved locally using bounded Luna/Terra work
  and primary integration, in `Circular/ZeroAreaExpansion.lean`. The prepared
  request is superseded; do not submit it.
- Earlier full-expansion observer stream interruptions were observation failures.
  The later deliberate cancellation is separately recorded above.

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

## General unicellular relation (completed and locally verified)

- Project ID: `7cac7db7-a2d1-4c27-8522-9b43c7690ed8`.
- Task ID: `2496607b-8e35-455c-9ee7-7a60c6ef4618`.
- SDK query confirmed `COMPLETE`, 100 percent, on 2026-09-25.
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
- Completed export is retained as `result.tar.gz` and selected source as
  `completed-candidate.lean`. All original supplied declarations and proofs
  were preserved. Luna ported the added declarations into `Unicellular.lean`.
- Local Lean 4.34 needed staged simplification: remove finite-set filter
  membership before rewriting resolved path steps, to preserve matching of
  dependent decidability instances. No statement or semantic change was made.
- The batch containing `Unicellular.lean` and `ColoringSwap.lean` passed the
  full build and all 62 public axiom checks. Only standard Lean axioms occur.

## Restricted swap sum (completed and locally verified)

- Project ID: `8099d4f4-4cb0-4b15-b617-ce2a18f3ee54`.
- Task ID: `6e7dc2fe-1962-4412-aeec-cac660f99fa4`, confirmed `COMPLETE`.
- Request directory: `/lake-cache/ai-projects/requests/VerticalStripLLT/swap-sum`.
- Uses five checked source modules and the same isolated Lean/Mathlib v4.28
  setup. The new pair embedding swaps both vertex coordinates.
- Target: the sum of coloring weights with `c a < c b` equals `C(q)` times
  the sum with `c b < c a`, assuming `(a,b)` is normal, strict edges are
  swap invariant, and the normal edges with `(a,b)` erased are swap invariant.
- This is a graph-conditional ingredient of the single-bounce proof, not a
  claimed path bounce theorem. The scanner work must prove these hypotheses.
- Supplied helpers include the checked coloring swap involution, increasing/
  decreasing coloring equivalence, and monomial preservation. The requested
  new work is admissibility invariance, ascent change, and sum reindexing.
- Completed archive retained as `result.tar.gz`; selected source extracted
  as `completed-candidate.lean`. Existing supplied statements were unchanged.
  Luna ported additions into `SwapSum.lean`. Primary fixed the final
  involution-coercion elaboration and updated conditional-rewrite names.
- The local batch included `BouncePath.lean` and `PrefixScanners.lean`.
  Full build and all 74 public axiom checks passed with standard axioms only.

## First bounce identity (completed and locally verified)

- Project ID: `30bbdfee-3932-4a5d-84a7-bd0d29bf82e2`.
- Task ID: `80bb72e2-fde2-415c-af6e-ffef30b9da06`, confirmed `COMPLETE`, 100 percent.
- Completion observed 2026-09-25 18:50 UTC; completed archive downloaded as
  `result.tar.gz` and selected source as `completed-candidate.lean`.
  The existing supplied definitions are unchanged; the added proof includes
  the scanner geometry, edge symmetry, and coloring involution.
- Request directory: `/lake-cache/ai-projects/requests/VerticalStripLLT/first-bounce`.
- Self-contained snapshot of fourteen checked local modules, including all
  swap-weight lemmas, prefix scanners, valid path swaps, and unicellular helpers.
- Exact target `coloringLLT_firstBounce` takes the source word
  `(U ++ [north,north] ++ V) ++ [diagonal,east] ++ W`, its validity, no east
  steps in V, the prefix-height return condition, and the endpoint gap.
  It must prove `G_P = C(q) * G_Q` for the constructed valid swapped path Q.
- The request must prove graph symmetry and changed edges from these word
  hypotheses; a graph-conditional substitute does not complete the target.
  `docs/archive/completed-plans/BOUNCE_PLAN.md` records the independently audited exact interface and
  the common-background and piecewise-coloring-bijection proof outlines.
- Service uses Lean/Mathlib v4.28.0. Conditional rewrite names in the isolated
  snapshot were translated from `ite_eq_left/right` to `if_pos/neg` for that
  environment; the local source and pinned dependencies are unchanged.
- Luna ported four separate scanner, graph, weight, and final theorem modules.
  Primary fixed a path-step simplification and a command-scope issue; the
  unchanged Lean 4.34 full build and all 101 public axiom checks pass.
  Only standard Lean axioms occur. Terra independently audited source fidelity.

## Second bounce identity (completed and locally verified)

- Project ID: `6bc089d7-87cb-4db2-b199-f4c4b4d05ee3`.
- Task ID: `eccb0402-2bde-4fbe-8eaf-19847e0f41ca`, confirmed `COMPLETE`.
- Completed 2026-09-25 19:13 UTC; archive and selected completed source
  retained in the request directory. Terra audited unchanged source semantics
  and exact boundary cases. Luna ported four modules; primary fixed namespace,
  list normalization, and finite-set simplification details.
- Local full build and public axiom audit passed. The coloring recurrence
  bundle is also checked; no recursive object or expansion is assumed.
- Request directory: `/lake-cache/ai-projects/requests/VerticalStripLLT/second-bounce`.
- Submitted 2026-09-25 with nineteen locally checked source modules, including
  the first-bounce scanner, graph, and weight helpers and the valid second
  successor. Environment remains isolated Lean/Mathlib v4.28.0.
- Exact target `coloringLLT_secondBounce`: for valid `U d n V d e W`, no east
  steps in V, the return equation and gap, prove equality with
  `U n d V e d W` for every finite alphabet.
- The prompt includes independently audited graph equations for the common
  background `U e n n V e e n W` and the interval-based coloring involution.
  Graph identities must be derived from the word hypotheses; no new graph
  assumptions or replacement semantics are accepted. No division is needed.
- Observe this same task; do not restart merely because an observer expires.

The API credential is loaded by the shared environment helper and is never
passed on the command line or stored in this repository. Do not upload the
workspace or reference snapshot wholesale; requests contain only needed inputs.

## Third single-bounce identity (completed and locally verified)

- Project ID: `13d18bc3-ffad-4cb1-9807-9b4d3cb4cb04`.
- Task ID: `372dfa89-c025-4779-8611-1fad2f31a341`, confirmed `COMPLETE`
  (2026-09-25 19:33 UTC). Archive and selected completed source are retained.
- Request directory: `/lake-cache/ai-projects/requests/VerticalStripLLT/third-bounce`.
- Contains twenty-four checked source modules in the isolated Lean/Mathlib
  4.28 environment. The sole target asks for valid Q=`U nd V ed W` and
  R=`U dn V ed W`, and `G_(U nd V de W)=(q−1)G_Q+qG_R` for every alphabet.
  Validity, return, gap, and no-east middle hypotheses match the third
  single-bounce case. Target validity must be proved, not assumed.
- The prompt supplies the shared background and exact changed-edge plan,
  and warns against applying a restricted-middle recurrence to eV. This
  concrete coloring theorem does not assert the generic restricted-recurrence
  implication discussed in `RESTRICTED_BOUNCE_AUDIT.md`.
- Luna ported path, helper, and final theorem modules. Primary repaired targeted
  imports and list normalization. Terra independently audited the exact target,
  derived prefix gap, legitimate unrestricted helper, and seven-equation
  cancellation argument. Local full build and all 146 public axiom checks pass.
  Existing supplied definitions are unchanged; the extra tactic import is
  `Mathlib.Tactic.LinearCombination`.

## First-east product reduction (completed and locally verified)

- Project ID: `48e8781d-7ebb-4e80-a093-9bd7e674cf0c`.
- Task ID: `22c118e9-b109-4fcc-9854-d93bfd73c353`, confirmed `COMPLETE`
  (2026-09-25 19:44 UTC). Luna ported the candidate into `ProductReduction.lean`.
- Request directory: `/lake-cache/ai-projects/requests/VerticalStripLLT/first-east-split`.
- Seventeen checked source modules, isolated Lean/Mathlib 4.28 snapshot.
- Exact target `firstEast_product_reduction`: from a valid first-east word,
  gap one and at least two east steps, produce two valid factors with positive
  sizes, both strictly smaller than n, and factorization for every supplied
  invariant satisfying `SatisfiesRecursion` in a commutative ring.
- The task must prove strict size bounds and dependent path identification;
  merely splitting words or assuming positive factor sizes is insufficient.
- This generic product branch uses no extra bounce relation or coloring
  semantics, so it is independent of the restricted-bounce audit obligation.
- Primary reviewed and verified the port: full/default build (1429 jobs),
  all 155 public axiom checks, and source/reference guards pass.

## Restricted first bounce with one leading east (target not proved)

- Project ID: `09862def-0239-41ee-a563-b12536df8d1f`.
- Task ID: `1d8ce50d-cbb5-44fb-9f5a-a6680f35a163`, terminal `COMPLETE_WITH_ERRORS`
  (2026-09-25 20:11 UTC).
- Request directory: `/lake-cache/ai-projects/requests/VerticalStripLLT/restricted-east-middle`.
- Twenty-two checked modules, isolated Lean/Mathlib 4.28 snapshot.
- Exact target `firstBounce_eastMiddle_of_recursion` extends the first-bounce
  equation to middle eV, where V has no east step, for an arbitrary invariant
  satisfying the existing restricted recurrence in `MvPolynomial σ Q`.
- The prompt explicitly excludes assuming uniqueness, third bounce, an
  unrestricted recurrence, or coloring semantics. It records the circular
  local diagram and the need for a new global argument. This is an open proof
  search, not an established implication. Observe this same task.

## Orientation column (service rejected submission; completed locally)

- Request directory: `/lake-cache/ai-projects/requests/VerticalStripLLT/orientation-column`.
- Eight locally checked modules, 560 lines, isolated Lean/Mathlib 4.28 snapshot.
- Target: `orientationExpansionAt_column k z`, uniform in `z : Polynomial ℤ`.
  Unique orientation, strict-chain reachability, constant HRV, and one fiber
  give `elementary k.succPNat`. Terra independently audited the proof outline.
- Submission on 2026-09-25 was rejected: too many projects in progress. No
  project/task ID exists. Do not cancel the generic bounce search to make room.
  Luna implemented the local proof; primary repaired API/type details and
  verified the column bridge. Full/default build (1436 jobs), all 176 public
  axiom checks, and source/reference guards pass. Do not resubmit this target.

The restricted-bounce archive contains an unchanged target with its placeholder,
plus `firstBounce_eastMiddle_not_derivable_up_to_size_four`, a separate bounded
candidate. Terra audited clause coverage, enumeration completeness arguments,
and source preservation read-only. It is not locally verified or imported.
Its `e ≡ 1` witness does not disprove the full recurrence, nor the manuscript's
specific elementary-generator setting. See `RESTRICTED_BOUNCE_AUDIT.md`.
A remote namespace-closing repair preserves local Lean EOF scoping; primary
made that close explicit in `ThirdBouncePath.lean` for future flattened inputs.

## Orientation multiplicativity (completed; locally checked)

- Project ID: `1d37e685-a581-4682-9b48-08fdcd5f3be6`.
- Task ID: `d1be4127-7c06-4481-b02c-2da410c82198`, confirmed `COMPLETE`
  (2026-09-25 20:20 UTC).
- Request directory: `/lake-cache/ai-projects/requests/VerticalStripLLT/orientation-concat`.
- Ten checked modules, 922 lines, isolated Lean/Mathlib 4.28 snapshot.
- Exact target `orientationExpansionAt_concat`: multiplicativity for every
  pair of valid paths and every ascent parameter z, including zero-size paths.
- Supplied graph block identities are already checked. The job must prove
  the orientation equivalence, HRV transport, fiber and ascent factorization,
  and finite sum identity. No coloring/expansion equality or recurrence law
  may be assumed. Observe this same job; returned proofs need local validation.

The multiplicativity candidate preserves every supplied module byte-for-byte.
Luna split it into `OrientationConcatSplit`, `OrientationConcatHRV`, and
`OrientationConcat`. Primary repaired the final namespace and the two
`ReflTransGen.lift` calls (4.34 makes endpoint arguments explicit), then
verified the focused targets. No semantic definitions were changed.

## Orientation unicellular relation (completed; locally checked)

- Project ID: `17bb2b30-57ab-40bf-b054-9640ec896ffc`.
- Task ID: `188a6fed-48fe-4246-99e8-26055f8683ba`, confirmed `COMPLETE`
  (2026-09-25 20:34 UTC).
- Request directory: `/lake-cache/ai-projects/requests/VerticalStripLLT/orientation-unicellular`.
- Sixteen checked modules, 1243 lines, isolated Lean/Mathlib 4.28 snapshot.
- Exact target `orientationExpansionAt_unicellular`: for every valid U d V
  and coefficient parameter z, the NE-minus-EN expression is C(z) times D.
- Inputs include the checked marked-edge identities, fresh-edge orientation
  equivalence and ascent count, upward-step effect, and HRV congruence. The
  proof must establish the true/false orientation bijection and finite sums;
  no coloring/expansion equality may be assumed. Observe this same job.

The integrated multiplicativity/helper/certificate batch passed the default
local build (1446 jobs), all 212 public axiom checks, global source guards,
and immutable-reference checks. The unicellular candidate has now returned and is being ported.

The unicellular diff preserves every supplied statement and definition. Its
only supplied-proof edit repairs `orientationAsc_insert` for Lean 4.28; this
edit is unnecessary locally and is not imported. New lemmas are grouped as
orientation transport, insertion sums, and the final unicellular relation.
Luna owns the three new modules; primary retains local verification.

The three unicellular modules pass the local focused build. The supplied
4.28 normalization repair was not ported; the original checked4.34 helper
remains unchanged. Ordinary and shifted specializations are also checked.

## Orientation first bounce (completed; locally checked)

- Project ID: `5546ba1c-a34c-4605-9485-a4e42436e5bd`.
- Task ID: `5964d41a-b920-4466-9490-fcc39d4de751`, confirmed `COMPLETE`
  (2026-09-25 21:13 UTC).
- Request directory: `/lake-cache/ai-projects/requests/VerticalStripLLT/orientation-first-bounce`.
- Twenty-five checked modules, 2109 lines, isolated Lean/Mathlib4.28 snapshot.
- Target `orientationExpansionAt_firstBounce_general`: unrestricted V,
  multiplier `C(z+1)`, valid NN source and explicit endpoint return/strict gap.
- Read-only manuscript excerpts contain the NN maps, HRV cases, and table.
  The job may return modular partial progress; no HRV preservation, semantic
  equality, or recurrence may be assumed. Primary and Terra identified the
  changing strict edge and HRV-block switching as the substantive obstacle.
- Observe the same project/task; local verification is required before integration.

The integrated unicellular/geometry checkpoint passed the default local build
(1454 jobs), all 235 public axiom checks, and global source/reference guards.
Only standard Lean axioms occur; all local candidate ownership is released.

The NN candidate was downloaded and inspected on 2026-09-26. Its supplied
input prefix is byte-for-byte unchanged (82,141 characters). Seven new helper
groups separate general reachability maxima, orientation operations, upward
relations, distinguished-vertex formulas, HRV transport, matching, and sum
assembly. The roughly 1170-line proof is ported into eight modules and locally checked.
The only proof repair replaces `ring` by `ac_rfl` for ascent-count addition;
the conditional API names and `push Not` syntax follow local Lean4.34.
Terra independently checked statement fidelity, HRV bridges, and the matching
bijection. Ordinary/shifted corollaries use narrow coefficient equalities.
The independent generalized NN reduction meanwhile passes the local default
build (1463 jobs) and all 259 public axiom checks.

## Orientation second bounce (completed; locally checked)

- Project ID: `432e553c-fc15-4226-8795-9bc0b1786b28`.
- Task ID: `fa04e12e-eb5d-43e6-ac50-92e432384704`, accepted
  2026-09-26 06:55 UTC.
- Request directory: `/lake-cache/ai-projects/requests/VerticalStripLLT/orientation-second-bounce`.
- Target `orientationExpansionAt_secondBounce_general`, unrestricted middle V
  and parameter z, equality with the DN successor and no scalar multiplier.
- Inputs reuse the checked NN helpers and the checked DN path/graph modules
  in an isolated 4.28 snapshot. Manuscript excerpts include the DN bijection
  and table. No recurrence or semantic bridge may be assumed.
- Observe this same project/task; local verification remains authoritative.

The DN job completed 2026-09-26 07:15:16 UTC. Its supplied prefix (142029
characters) and exact target statement are unchanged. Luna ported seven helper
modules plus the final theorem; all eight pass local4.34 compilation. Terra
independently audited the actual upward-step bridges, finite matching bijection,
HRV conjugation (including the special corner vertex), and unrestricted V.
No semantic assumption or hidden no-east restriction was introduced.
The ordinary expansion now follows locally through the proved recurrence
certificate and uniqueness; remote results alone were never authoritative.

## Periodic adjacent swap (completed and locally checked)

- Project `bbfa6e2c-81bb-45ad-b68d-7737d8386f28`, task
  `8a5b564d-cdc3-4d8e-9b8b-04ff141b7d5b`, COMPLETE on 2026-09-26.
- Request/results: external `periodic-adjacent-swap/` directory under the usual
  VerticalStripLLT request root. Exact three modular/order statements retained.
- Ported to `Circular/PeriodicSwap.lean`; only tactics/imports changed for
  local 4.34, and the unused translation parameter is named `_hn`.
  The involution, periodicity, and strict order on separated pairs all compile.
- Primary added the independently checked circular residue projection and
  actual lifted-HRV/fiber-monomial applications. No recurrence is assumed.

## Periodic natural-edge boundary swap (completed and locally checked)

- Project `6cffe7ef-5943-458b-8619-dd7e2b17ac8f`, task
  `502e5215-4324-49e9-a0c7-3146ddc18f60`, COMPLETE on 2026-09-26.
- Request/results: external `periodic-boundary-swap/` directory.
- Exact target `periodicSwap_boundary_relation` proves natural lifted-edge
  invariance after excluding the periodic adjacent bridge. Its assumptions
  are periodicity, equal adjacent boundary values, and avoided gap values.
- The returned helpers and target are ported to `Circular/PeriodicBoundarySwap.lean`
  and locally compiled; source statements and supplied prefix are unchanged.
  This is a local exterior-incidence theorem, not the circular expansion.

## Circular NN orientation recurrence (completed and locally checked)

- Project `4c8c3a9f-a32a-4643-92c4-c2f09d633686`, task
  `4e3adb0d-712e-4539-9487-7d388cd71335`, submitted 2026-09-26.
- Request/results: external `circular-nn-orientation/` directory; exact statement
  in `Target.txt`, module snapshot in `INPUT_MODULES.txt`.
- Target `Diagram.shiftedOrientationExpansion_shortenStrict_NN`: the actual
  circular HRV expansion equals `(X+1)` times the expansion of the constructed
  shortened strict-corner diagram, under geometric NN contact hypotheses.
  It does not ask for the full expansion or repeat the proved base cases.
- Supplied 34-module checked prefix, adapted to isolated service Lean 4.28,
  includes actual HRV conjugacy, periodic swap, and target edge-set changes.
- A file supplement was rejected because uploads require an idle project.
  No new task was created by that rejection. The checked boundary-swap proof
  was then sent successfully as text INSTRUCT to the same active task.
- Task COMPLETE on 2026-09-26. Returned `result.tar.gz` and
  `completed-candidate.lean` are retained externally, with per-module slices.
  The service reports the exact target compiled with standard axioms only.
- Only new helper proofs are ported; prefix repairs for service 4.28 are not
  imported. The supplied periodic-boundary helpers reuse our already checked
  module. Eight modules separate HRV potential comparison, local geometry,
  edge swaps, orientation subsets, target reindexing, local identity, matching,
  and sum assembly. Primary owns local integration and verification.
- The local identity partitions four source configurations; HRV potential
  comparisons prove the unchanged-monomial cases and acyclicity. The periodic
  swap matches the bottom pair, while path substitution matches the top pair.
  The statement remains the actual NN recurrence, with no recursion hypothesis.

The candidate's final theorem now passes local Lean 4.34 verification. The
input prefix's service-specific repairs were not imported. Local proof repairs
supply explicit relation endpoints for `TransGen.mono/lift`, unfold `Function.onFun`
where required, and use the current conditional API. Two unused hypotheses were
removed from auxiliary lemmas; the requested final theorem is unchanged. The
independent Astra audit confirms actual lifted-HRV semantics and all cyclic
cases, with no ordinary-cut or no-wrap assumption. The coloring recurrence and
area-decrease theorem are proved separately and combined into a checked NN
semantic induction step. Generalized DD propagation and the other bounce
identities remain open.

## Circular direct DN orientation recurrence (completed and locally checked)

- Project `a768ca01-7392-49a9-b695-339de82ec027`;
  task `847a2439-f8d6-4124-8cb3-222377ca36f9`.
- External request directory `circular-dn-orientation/`, 55 checked input
  modules, exact final target in `Target.txt`.
- Target: original `shiftedOrientationExpansion` is unchanged by actual
  `dnSuccessor`, using constructor hypotheses and direct contact `f.tail=e.head`.
- Strategy: generic lifted HRV diamond on each side, identical top reachability,
  periodic adjacent-swap bottom matching; cyclic states contribute zero.
- The source includes checked NN potential/conjugacy machinery. Local coloring
  DN was proved independently while the remote job ran.
- Observer reconnected after one stream interruption; same project/task.
  The exact target is now locally verified in `SecondBounceOrientation.lean`.
  Generic triangle and endpoint-pair helpers are separate modules. Existing
  local corner-boundary and normal-pair formulas replace duplicate service
  proofs. `SecondBounceRecurrences.expansion_iff_secondBounce` (namespace
  `Diagram`) combines the independently proved coloring and HRV identities.
  No statement, definition, or axiom from the service prefix was substituted.

## Circular overlapping ND reduction (locally integrated)

- Project `eb5bc1c3-b026-45aa-9acb-6d3927797294`, task
  `55de8e35-31e7-4ff2-a476-f26ac24fe345`.
- External request/observer directory: `circular-nd-alias/` under this project's
  requests cache. Submitted after the DN task completed; one remote task active.
- Exact target `exists_nd_alias_reduction`: valid target, doubled-area drop six,
  actual coloring factor q, and actual shifted-HRV factor q+1, for the full
  periodic overlap branch of an acyclic reverse bounce.
- The named constructor, strict-pair relation, measure, and search realization
  were supplied as fixed support. The exact final theorem now passes the local
  pinned toolchain in `AliasRecurrences.lean`; eight modular helpers preserve
  actual winding and HRV semantics. Primary added shifted coloring, target
  acyclicity, and `expansion_of_nd_alias`. The service prefix was not imported.
- Independent Astra audit found no extra final hypotheses or semantic changes.
  Compatibility edits were `lia`, explicit transitive-closure endpoints, and
  current tactic names. Full build: 1818 jobs; axiom inventory: 1307 declarations,
  only propext, Classical.choice, Quot.sound.

## Circular resolved DD child (locally integrated)

- Project `9dedc3e9-472c-4e5e-aa74-14f185dc95e1`, task
  `e598f460-d1cc-4c7c-add6-cccf40042f96`.
- External request/observer directory: `circular-dd-resolved-child/`.
- Exact target `DDLocalData.resolved_dd_child`: raised-root eligibility, one
  fewer DD contact, preserved terminal flags, and inherited strict acyclicity.
  Inputs are the concrete local geometry, actual counted search, eligible root,
  source acyclicity, and NN/DN terminal flag. No recurrence assumptions.
- The 78-module geometry-only request omits downstream polynomial identities
  from three modules, retaining their definitions and hypotheses unchanged.
  It supplies checked resolved row formulas, full deletion-child transport,
  and main/parallel contact separation.
- Remote proof completed and was ported into `BounceIterates`,
  `DDResolvedTransport`, and `DDResolvedChild`. Primary repaired current API
  compatibility without changing the checked prefix or target hypotheses.
  Full local build: 1824 jobs; axiom inventory: 1338 declarations, standard only.

## Circular interior-overlap one-bounce restart (locally integrated)

- Project `6654bca9-3649-4ebd-b9b8-ae1cc3050caa`, task
  `0f992037-5575-4c13-bd41-75c4694b8651`.
- External request directory: `circular-interior-restart/`.
- Exact target `DDLocalData.exists_oneBounce_restart_of_interior_overlap`:
  an acyclic eligible counted ND search whose upper terminal aliases an
  interior main contact acquires an eligible zero-DD NN/DN restart in the
  actual resolved diagram. Independent Astra review checked the indexing.
- Uses the completed DD geometry prefix; no new polynomial assumptions or
  generalized R4 identity. Completed remotely with only standard axioms.
- Luna ported the final theorem only into `InteriorRestart.lean`; primary checked
  it locally against the unchanged project definitions and helpers. No prefix
  replacement, added hypotheses, or local proof repairs were needed beyond
  current tactic names.

## Circular direct one-bounce ND (locally integrated)

- Project `7f814d1b-422f-469b-b0f8-cc2696e9518e`, task
  `bc03be2f-39de-4689-ba9b-4ab97ef9bb9c`.
- External request directory: `circular-direct-nd/` (110 dependency modules).
- Exact target `Diagram.exists_oneBounce_nd_reduction`: valid targets with
  doubled-area decreases two and four, the actual coloring identity with
  coefficients q−1 and q, and the actual shifted HRV identity with coefficients
  q and q+1. Inputs are an eligible zero-DD ND search; no acyclicity hypothesis.
- The [local proof plan](proofs/CIRCULAR_DIRECT_ND.md) gives seven actual NN/DN/R1
  identities. Source hashes and module list are retained with the request.
  Completed remotely; Luna ported `StrictVals`, `OneBounceNDGeometry`, and
  `OneBounceND`. Primary restored the truncated final export and repaired
  transparency/tactic compatibility. All three pass the local pinned toolchain.
  Primary added `OneBounceNDRecurrences` to discharge the area-induction branch.
  Independent Astra review checked the seven actual identities, cyclic
  intermediates, shift injectivity, and exact hypotheses. No prefix replacement.

## Circular full DN elimination (locally integrated)

- Project `ae819e79-2742-4965-9254-8eef5929cfa0`, task
  `0216c708-f9a4-4baa-82d0-d98d33d8e293`.
- External request directory `circular-full-dn/`, 118 dependency modules.
- Exact target `Diagram.exists_dn_reduction`: actual coloring and HRV identities,
  preserved half-square area, inherited strict acyclicity and decreased strict
  rank for any eligible DN search in a strictly acyclic diagram.
- The task explicitly requests elimination by direct DN and R1, with counted
  child searches and a concrete closing triple. No projected ND/R4 relation,
  new recurrence hypothesis, or no-wrap restriction. Source hashes and exact
  target are retained externally. The task is complete; observer 48054 finished.
- Luna extracted `DNReductionTarget`, `DNReductionDiamond`, and `DNReduction`.
  Primary repaired imports and checked them with the local pinned toolchain,
  then added `FullDNRecurrences`. Existing shift-injectivity declarations moved
  unchanged to `QShiftInjective` for shared use; the service duplicate was omitted.
- Independent Astra audit confirmed concrete target identification, valid
  count induction, cancellation, cyclic intermediate handling, and unchanged
  final hypotheses. The remote flattened prefix had proof-script compatibility
  edits and one duplicate theorem omitted; none of that prefix was imported.


## Circular separated-contact ND (active)

- Project `361812e0-b73e-48b9-9ad7-dffe103615f6`, task
  `e58bd214-3a7c-4d47-ab01-e58521c293ad`; observer session 45949.
- External directory `circular-separated-nd/`; 175 checked modules from
  `0fc4d07`, exact target and source hashes retained.
- Target `Diagram.exists_nd_separated_reduction`: the two actual ND identities
  and area drops two/four when the terminal upper vertex avoids every strict
  main head, including the root. All overlap cases remain separate obligations.
- The request uses full NN/DN and four R1 identities, requiring concrete contact
  transport and careful handling of cyclic lowered intermediates. It includes
  `neutralExchange_acyclic_iff` and the normal-comparability semantic base.
  It explicitly forbids strengthening separation to a global no-wrap condition.

## Circular interior-overlap semantic step (prepared; capacity-limited)

- External directory `circular-interior-expansion/`, the checked prefix plus
  `DoubleCornerReduction` from `eb11c69` (176 modules), unchanged target and
  updated hashes/proof-development notes. No remote project/task was created.
- Target `Diagram.expansion_of_nd_interior_overlap`: saturated, strictly acyclic
  source, actual eligible counted interior ND overlap, and the semantic bridge
  for every smaller outer measure imply the source bridge.
- The concurrent submission was rejected because the account had too many
  projects in progress. Submit the saved request when the separated-ND job
  completes; no repeated retry loop or cancellation of other tasks.
- The proof notes retain the failed fixed-length slide/rank shortcuts and the
  coefficient-one rotation cancellation issue. They ask for a proved exit,
  using actual recurrences and semantic bases, not a new hypothesis hiding it.
