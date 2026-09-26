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

## Full circular elementary expansion (active)

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
- During this run, primary used INSTRUCT to inform the same active task that
  the entire zero-normal family is already proved locally (`b7fe916`), and to
  focus on all-corners-strict positive-normal-area reductions. No restart or
  cancellation occurred. Exact steering is retained as `STEERING.md` in the
  request directory. Live corner-reduction candidates are not locally proved
  until exported, audited, and compiled.
- Primary owns the live observation and eventual candidate audit. No claim
  that the full circular theorem is proved is made at submission.

## Circular zero-area expansion (capacity rejection; now proved locally)

- Request directory:
  `/lake-cache/ai-projects/requests/VerticalStripLLT/circular-zero-area`.
- Exact target `coloringLLT_shifted_eq_expansion_of_no_normal`: the full
  arbitrary-size zero non-strict area family, for every finite alphabet.
- Prefix includes the checked general HRV foundations, zero-area edge bounds,
  strict-cycle vanishing, HRV roots, and the general strict-chain enumerator.
- Submission on 2026-09-26 was rejected by the service's concurrent-project
  limit. No project or task was created. The main full-expansion request
  remains active and takes priority; no task was canceled to submit this.
- This family was subsequently proved locally using bounded Luna/Terra work
  and primary integration, in `Circular/ZeroAreaExpansion.lean`. The prepared
  request is superseded; do not submit it.
- The full-expansion observer has repeatedly lost its stream connection; a fresh
  task query confirmed `IN_PROGRESS`. This is an observation failure, not a
  failed or canceled proof request. Resume the same project when monitoring.

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
  `docs/BOUNCE_PLAN.md` records the independently audited exact interface and
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
