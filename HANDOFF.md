# VerticalStripLLT handoff

## Current overlapping-corner checkpoint

2026-09-28, continuation from clean pushed `6e296bc`. The goal remains
active: prove general decreasing recurrences with whole-component
reconstruction and identical coefficients for K and E. The remembered
sixteen-case example has not been identified; the preceding four-edge
note gives a new explicit sixteen-row table.

See [overlapping corners](docs/proofs/COMPONENT_OVERLAPPING_CORNERS.md).
For source area01233 with strict03,14, NN14 reconstructs the two remaining
connected non-tree, not wholly mixed-cyclic components, of sizes34 and32.
The first canonical image is already complete. For the second, adding
`[246]−[181]=0` completes two target components simultaneously, and a
redundant-edge cancellation gives seven whole components of area01232.
Both identities extend to arbitrary exterior components meeting the core
only at0,4 with no exterior undirected path joining them. Astra audited
the corrections, completeness and exterior extension.

See [closure repair tests](docs/proofs/COMPONENT_CLOSURE_REPAIR_TESTS.md).
After the source NN split, equal reachability and the single safe NN swap
suffice to reconstruct all31 source components in five selected fixtures.
Largest target:32768states,6931classes,2639components. Every certificate
passes original class-sum checks and exact K/E evaluations. This is finite
evidence, not a uniform reconstruction theorem. Restricting to components
containing class-maximal representatives FAILS, even with a joint solve
retaining all free parameters. The class-minimal restriction also FAILS.
The note records precise counterexamples. Do not revive either restriction
as proved, or interpret their failures as failure of full reconstruction.
The whole-component redundant normal edge addition/deletion lemma is valid
under its throughout-the-component redundancy hypothesis.

Receipts and frozen sources:
`/lake-cache/ai-projects/requests/VerticalStripLLT/overlapping-corners/`.
Use `canonical_pieces.jsonl`, `local_certificates.jsonl`, and the final
`capacity_minimal_repair.jsonl`; README gives commands/provenance and
SHA256SUMS.json hashes20files. Intermediate capacity receipts are retained
and labelled historical. All owned jobs finished exit zero; no live job.

Primary owns the proof notes/index/handoff and external Rust consumers,
and retains the sole Lean build slot. Existing Astra simpler_component_route
worked read-only/build-free; its bounded audit of both new notes is complete.
The requested redundant-edge proof clarification is incorporated.
Other existing agents are idle with no assigned file edits.
No new worker/account, Claude process, Lean build, manuscript edit or
maintained Rust source edit. Runtime registry, MCP list and Rust
capabilities were checked; Lean MCP still targets the other project.
Shared Rust HEAD is d53fb193af3c69adedbd9ec8592f87235d809ffa, clean.
The reusable flip API proposal remains suggestions/flip-enumeration-api.md.

Next: find a uniform construction of the whole-component repair, retaining
all needed target components. The finite class-incidence solves suggest
a stronger NN claim using closure and one swap alone, but no solvability
or integrality theorem is established. DN/DD and general exterior
compatibility still require proof. Preserve the existing manuscript.

## Current four-edge reconstruction checkpoint

2026-09-28, continuation from clean `a0019dd`; the previous turn made proved
local progress. User clarified again that additional diamonds should repair
pieces into whole components, and recalled a sixteen-orientation case split.
The full goal remains active. We have not identified the remembered example.

See [four-edge cases](docs/proofs/COMPONENT_FOUR_EDGE_CASES.md):

- A sixteen-row table, with the remaining edge orientation as exterior data,
  tracks the canonical NN image of the five-state K4 component. Exactly two
  target components have nonconstant coefficients. Adding the zero relation
  `[bcde]−[bce]` completes BOTH; then `[acde]−[ace]` cancels. Thus the
  original component becomes four complete corner-deletion components.
- This C5 recurrence holds uniformly with ANY whole exterior component
  attached only at the maximum vertex: the NN swap fixes that exterior.
  It includes cyclic exterior components and is independently Astra-audited.
- Four paired diamonds and the safe internal swap (1 2) reconstruct the
  eight-state K4 tree component into four whole components. The same proof
  works with arbitrary exterior components meeting the core only at its
  ends, provided no exterior path joins those ends. Two outputs disconnect
  interior vertices; the other two delete the strict corner. These are
  legitimate vertex/area induction terms, even with exterior cycles.
- Cartesian products here are products of STATE SETS; valuations are on
  their unions. No polynomial factorization across articulation is claimed.

The Rust receipts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/component-reassembly/`.
`nn_four_bit_pieces.jsonl` checks both valuations exactly, all table entries,
every repaired target flip, and complete component lists. The C5 extension
has a 25-state check; the C8 extension includes a 40-state cyclic-exterior
check and attachment at both endpoints. Sources/receipts are frozen with
`SHA256SUMS.json`. All jobs finished with exit zero.

A separate bounded complete-graph experiment passes active connected
component uniqueness through n=7 (1,048,576 states and 34,558 components at
n=7). This is finite evidence only; it does not prove general component
closure. `complete_corner_components.jsonl` records its exact scope.

Primary owns the proof notes/index/handoff and external Rust consumers and
retains the sole Lean build slot. Astra `simpler_component_route` finished
read-only/build-free audits of both reconstructions and exterior extensions.
Luna `word_covers` considered only complete-graph root-helper flips; its
bounded assignment is finished. Its conditional five-flip helper requires
no exterior paths i→j, j→m or i→m and no exterior edge leaving 0;
it does not prove general connectivity and is not used in these proofs.
The exact statement is retained in the external receipt README. No delegated file edits,
new worker/account, Claude process, Lean build, manuscript edit, or maintained
Rust source edit. Runtime registry, MCP list, Rust guide/metadata and existing
APIs were rechecked. The source consumer only widened two helper visibilities
to reuse its exact valuation code; maintained API integration remains the
existing proposal in `suggestions/flip-enumeration-api.md`.

Next: use the four-edge table approach for arbitrary exteriors in each
decreasing recurrence. The proved attached-block classes do not replace
that requirement. Track whole target coefficient patterns and repair all
their incident flips together; do not stop at isolated state reductions.

## Current NN flip-interaction checkpoint

2026-09-28, continuation from clean `06655eb`. The user's full recurrence
proof goal remains active. We have proved local progress, not whole-component
closure. See [NN flip interactions](docs/proofs/COMPONENT_NN_FLIP_INTERACTIONS.md):

- Ordinary actual flips need cover tests at only one endpoint.
- With independent short pairs, two flips commute precisely when the four
  relevant edges cover in the formal final state. A failure has a redundant
  edge; a strict edge may be the only available one among those four.
- The shared-edge exceptions are exhaustive. A single paired diamond
  `[P]+[P−x+y]=[P−x]+[P−L+y]` handles all of them and decreases
  `(raw diagram area, selected-edge count, total selected-edge length)`.
- The common-short removal case can have all edges covering at all three
  states. Its diamond correction preserves the displayed q-preserving
  equality, but compatibility with other incident flips remains unproved.

External Rust receipt:
`/lake-cache/ai-projects/requests/VerticalStripLLT/nn-interactions/interaction_audit.jsonl`.
Four fixtures through seven vertices check 169,984 states and 1,063,936
one-endpoint cover comparisons, plus all mixed/preserving interactions.
All assertions pass, exit zero. These are structural checks, not fresh K/E
evaluations. The valuation identities have direct proofs and independent
Astra audit. Sources, manifest/lock and logs are frozen beside the receipt
with `SHA256SUMS.json`. The bounded job is finished; no live owned process.

Primary owns the proof notes/index/handoff and external Rust consumer, and
retains the sole Lean build slot. Existing Astra `simpler_component_route`
worked read-only/build-free on interactions; its bounded followup audited
a spanning-tree decomposition of whole q-preserving pieces. That identity
leaves a root residual in general and does not solve component reassembly.
The followup is finished, with no delegated file ownership outstanding.
Luna's bounded Abreu–Nigro review finished and supplies no new transport
theorem. A relabeling changing the ambient diagram is not by itself an
obstruction to cross-diagram transport. No new worker/account, Claude process,
Lean build, manuscript edit or maintained Rust source edit. Runtime registry,
`codex mcp list` and Rust guide/metadata/APIs were checked. The Lean MCP still
targets the other project and was not used. Maintained Rust API integration
remains the existing `suggestions/flip-enumeration-api.md` proposal.

Next: extend the paired corrections along complete q-preserving pieces,
handle their residuals, and regroup emitted states into whole smaller
components. Do not treat decreasing individual states as completed induction.

## Current NN continuation

2026-09-28, continuation from `ca02d67`. Previous turn made proved and exact
computational progress; this turn adds a four-diamond LEFT-to-RIGHT transfer.
The user's full goal remains active: a combinatorial component HRV proof
using the decreasing diagram recurrences, with the same reconstruction on
colorings. Whole-component closure remains unproved; no completion claim.

See [the left NN transfer](docs/proofs/COMPONENT_NN_LEFT_TRANSFER.md):

- Saturation supplies a strict corner ud crossing the NN corner ac and
  containing the retained left-overlap edge tb, with u≤t<a<b<d<c.
- When u=t, four ordinary diamonds transfer a left difference to a right
  difference with explicit terms in the further corner-deletion diagram.
  The valuation identity is unconditional. The actual flip paths and
  coefficient interpretation require the stated covers.
- The local cases where that corner is redundant are completely split:
  either delete it at both endpoints, or use one diamond to leave a
  term with fewer selected edges and two corner-deleted terms.
- When u<t and a covering edge ut is selected, two actual flips move the
  left difference to a td-supported transfer. Since td is then normal,
  its remainder stays in the same ambient diagram; this does not yet
  establish an area decrease or provide ut in general.
- If a q-absent state admits two different flips inserting q, either
  endpoint has the other triangle's normal long redundant. Deleting that
  edge preserves both valuations and lowers selected-edge count. Luna
  independently audited this competing-triangle lemma.

Primary owns the proof notes, index, this handoff and the external Rust
consumer. Existing Astra `simpler_component_route` derived and audited the
local results, read-only and build-free; its assignment is now finished.
Existing Luna `word_covers` audited the competing-triangle lemma, also
read-only/build-free and now finished. No file ownership was delegated.
No new worker/account/model/worktree, no Claude call, no Lean build, and no
manuscript or shared Rust source edit. Primary retains the sole Lean build
slot. Tool registry and `codex mcp list` were rechecked; the only Lean MCP
still has the wrong project root. Rust guide/metadata/APIs were rechecked.

All Rust jobs finished with exit zero. Main receipt:
`/lake-cache/ai-projects/requests/VerticalStripLLT/nn-left/seven_tall_left_complete.jsonl`.
It checks 4,096 arbitrary-exterior valuation identities, 1,288 actual
four-diamond transfers, 1,136 cases with both endpoints redundant, 136
remaining redundant-corner cases, and 544 earlier-starting-corner transports.
The maintained P-partition/HRV APIs check BOTH valuations exactly. Component
right-overlap tests pass for all 177 components of area012343, and all four
and six components surviving known reductions in area0123432 and0123434,
respectively. These are specified finite checks, not general theorems.
Frozen source, Cargo manifest/lock, receipts and hashes are in `nn-left/`.
No owned compiler, consultant or auxiliary assignment remains live.

Next: extend the paired transfers along every incident flip so that their
remainders are complete components, while controlling a decreasing measure.
The new local pairs need not exhaust their q-preserving components; arbitrary
component fragments still cannot be treated as solved. The conditional
covering edge ut and the RIGHT global compatibility also need attention.

## Previous NN checkpoint (`ca02d67`)


2026-09-28, continuation after `c83dffb`. The user wants a direct component
proof from the existing decreasing diagram recurrences: split one component,
redistribute with diamonds, and collect whole smaller components with the
same coefficients for colorings and HRV expressions. Rust is authorized for
studying the cases. The goal remains active; this turn made mathematical
progress but did not complete the uniform reconstruction.

Primary owns the recurrence notes, documentation index, this handoff,
`suggestions/flip-enumeration-api.md`, and the external Rust driver. No shared
Rust source, Lean source, or manuscript was edited. Primary retains the sole
serialized Lean build slot; no Lean build ran. Existing Astra
`simpler_component_route` audited the new overlap lemmas and counterexample;
its read-only/build-free assignment is finished. Luna's prior bounded audit
is finished. No new worker, account, model or worktree was introduced.

The [NN overlap note](docs/proofs/COMPONENT_NN_OVERLAPS.md) now proves:

- The canonical image of ONE component has constant coefficients across
  every smaller-diagram flip preserving ab. Only the left and right
  overlapping triangles that exchange ab remain.
- Right-overlap defects satisfy an antisymmetry identity. This gives a
  two-state correction for a background fixed by swapping a,b, and a
  four-state correction when there is a selected d-to-c path.
- A further actual bc-long diamond has a local decreasing measure:
  selected-edge count, then missing forward comparabilities. This is not
  yet a global termination argument.

The unrestricted four-state correction is false even for a saturated source.
Astra supplied a seven-vertex disconnected counterexample; independent Rust
BFS verifies its complete eight-state component, NN eligibility and defects.
The proposed correction has coloring multilinear coefficient 189−147=42,
although its HRV expression vanishes. Factoring disconnected components
removes this example, but does not prove the connected version. The unresolved
step is to propagate corrections along whole target components without
breaking earlier coefficient equalities; the left overlap also remains open.

The [direct NN note](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md) retains the
proved three-diamond example and initial split. Four six-vertex certificates
have been improved from rational expressions to positive integer sums of
whole smaller components. Two are single-component identities. All were
independently evaluated exactly for BOTH K and E using the maintained Rust
P-partition and HRV APIs. The local relation quotient also certifies the
expressions. These are finite examples, not an all-degree theorem.

All owned jobs finished. The authorized Claude left-overlap consultation
used the existing account/model, no tools, and a monitored 1,200-second cap;
it ended with timeout exit 124 and no usable assistant output. Do not treat
it as a proof audit. No Claude process remained in the subsequent process
check. Rust jobs exited zero; no compiler or consultant remains active.

External receipts: `/lake-cache/ai-projects/requests/VerticalStripLLT/nn-overlap/`.
`nn_rust_small_certificates.jsonl` contains the improved expressions;
`nn_boundary_classification.jsonl` and
`nn_saturated_attachment_audit.jsonl` contain the flip checks;
`nn_saturated_shield.jsonl` contains the seven-vertex counterexample.
The frozen Rust source and `SHA256SUMS.json` are in the same directory.
The prior source is retained as
`recurrence-continuation/nn_component_transport-at-c83dffb.rs`.
The driver reuses `component_source_probe.rs` and maintained exact Rust APIs;
the pending maintained-API integration is linked in the suggestion above.

The prior DD result remains valid: exact corner sectors give whole-component
packet transport and the ordinary measure is `(vertices, area sum, area moment)`.
Both Astra and Luna audited it; all 44 eligible saturated DD instances through
seven vertices passed the refined finite isolation test. Individual DD and
circular recurrence redistribution remain open. See
`docs/proofs/COMPONENT_DD_PACKETS.md`. Existing Lean proofs remain complete.

Earlier increment, 2026-09-28: persistent user goal is a combinatorial proof of the component
HRV formula. User explicitly prioritizes pushing components through the
recurrences and points to Abreu--Nigro's increasing forests. Previous turn
made proved mathematical progress; the goal remains active. Primary owns
recurrence research notes and all builds (none planned). Existing Astra
`simpler_component_route` completed its DN transport audit; existing Luna
`word_covers` completed its audit of the Abreu--Nigro comparison and ordinary
NN proof, including the prose and indicator strengthening. Both assignments
are released; no auxiliary process remains. Both were read-only/build-free. No new workers,
account changes or Claude calls. This continuation began at clean `e24da4a`.

Primary now owns `docs/proofs/COMPONENT_RECURRENCE_REDUCTION.md`, the linked
status corrections in `DN_COMPONENT_COMPLETION.md` and
`FLIP_COMPONENT_INDUCTION.md`, and the documentation index. Proved ordinary
NN reconstruction gives identical K/E recurrences in whole component packets.
The old DN one-active-component condition is false at n=7; the short exact
certificate and its repair by known reductions are recorded. NN has analogous
raw collisions at n=6. DN packets preserve weak vertex blocks and edge counts
in each block. After factoring disconnected states, tree cases and mixed-cycle
corner deletion, refined isolation passes all eligible saturated NN instances
through n=6 and DN through n=7. This remains a conjectural all-degree step.
NN class indicators actually map to indicators of unions of whole target
components: the source packet and target union have an explicit orientation
bijection, with semantic equality supplied by paired diamonds. The remaining
global isolation claim is still unproved. A concrete DN subproblem is lifting
the exceptional target-long ux rotation with connected mixed-acyclic source
endpoints and all actual target-cover hypotheses retained. DD coverage and
circular recurrence transport are also not completed. No builds or manuscript
changes. External receipts: `recurrence-continuation/`, with `SHA256SUMS.json`.
The user goal remains active; this turn made mathematical and diagnostic
progress, rather than merely restating the earlier obstruction.
Checkpoint `d77fb3f` records the new results; final audit clarifies that known
source corrections stay in the original diagram and are justified separately
by the earlier reductions. Mathematical audits, exact probes, and whitespace
checks passed. No assertion of a complete new component proof is made.

## Ordinary diamond-proof search: latest result

2026-09-28: user requests a more accessible general component proof using the
local diamond lemma. Primary owns research notes and the sole Lean build slot;
no Lean source or manuscript proof is being replaced during exploration.
Existing Astra simpler_component_route investigated a uniform auxiliary-poset
reduction; existing Luna word_covers audited source/sink branching and previous
obstructions. Both were read-only/build-free and have finished. The primary's
read-only nested Claude call reached its 20-minute timeout (exit 124) without
output; no Claude proof or audit result was obtained. Its request files remain
under external `diamond-proof-search/`. No new account or supervisor worker.
Rust capability check completed (library guide, Cargo metadata and semantic/API
search). A bounded external Python probe may orchestrate the existing flip
model and Rust HRV bridge, extending the earlier exact rational relation-span
probe; no existing Rust API exposes this auxiliary-poset diamond/swap quotient.
No new polynomial family or reusable computational library is being introduced.
Known false targets: fixed-diagram chain straightening, root-only promotion,
and confluent greedy critical-fork normalization. Auxiliary posets are allowed;
full component labels and exterior terms must remain controlled.

Primary owns `docs/proofs/COMPONENT_AUXILIARY_DIAMONDS.md` and its links in
`docs/README.md` / `DIAMOND_STRAIGHTENING_AUDIT.md`. New results, independently
checked by Astra: the auxiliary-diamond quotient is integrally the permutation
coordinate ring; a terminating diamond recursion reduces every forward poset
to increasing forests; certified whole-poset swaps give a maximal-letter
normalization. The note states the remaining universal factorization precisely.
Exact rational tests pass for every forward poset through n=5, and all 1710
ordinary components in degrees 2--5. This is evidence, not an all-degree or
integral proof. Pairwise identification of permutation terms is insufficient
already at n=4. Probe receipts are in external `diamond-proof-search/`.
Astra and Luna assignments are released; no consultant remains running.
The general diamond-based component proof was not obtained. The next precise
target is equation (5) in the new note, or a weaker component-specific forest
cancellation. Checkpoint `9e5013a` is pushed to `origin/main`; mathematical
proof audit, bounded exact probes and `git diff --check` passed. No Lean or
LaTeX source was changed and no compiler build was run in this search.

## Current manuscript

2026-09-28: completed the user's new separate circular-first draft in Overleaf:
`/home/paxinum/Dropbox/Apps/Overleaf/LLT flip/dyck-first.tex` and
`dyck-first.pdf` (12 pages, nine diagrams). The aggregate circular HRV proof
comes first, by unicellular/bounce relations and half-square-area/strict-rank
induction, including the column reversal. Ordinary components follow, with
word algebra in an appendix. The previous main/sections and all original
archives are preserved. See [manuscript synchronization](docs/MANUSCRIPT.md).

A follow-up restores the ordinary diamond lemma in Section 4.2 with an inline
four-state diagram. The valid local identities are distinguished from the
obstructed fixed-diagram chain-straightening proposal; the word argument supplies
the global component step. The updated 12-page preview builds without warnings
and the new page was visually inspected. No Lean change or build was needed.

Primary owns the new draft and metadata. Astra reviewed the circular argument;
Luna reviewed the ordinary argument and its historical route. Corrections and
notation clarifications are incorporated; assignments are released. The old
component recurrence outline was never the completed proof. The new ordinary
section follows the checked word/Cauchy/signed-sink approach.
`DYCK-FIRST-MAP.md` in Overleaf gives exact source correspondence and review
boundaries. Clean external LaTeX build, resolved references and visual checks.
No Lean source or build changed; no account, worktree or supervisor worker changed.

## Completed result

The requested **full circular component proof is formalized**, together with the
ordinary component theorem, common shifted q-weight, elementary positivity,
and weighted degree. No component proof obligation remains.

Public declarations in namespace `VerticalStripLLT.Circular`:

- `component_strict_eq_elementary_of_forward`
- `component_strict_eq_elementary`
- `component_weighted_strict_eq_orientation_sum`
- `component_weighted_strict_eq_eval`
- `component_weighted_e_positive`

See [the completion audit](docs/COMPONENT_COMPLETION.md) for exact statements,
source correspondence and proof modules. The ordinary theorem is in
`Components/OrdinaryComponentExpansion.lean`; the circular result is in
`Components/ComponentExpansion.lean`. Both are main-library imports.

They use the actual complete global flip component, strict-coloring sum and
HRV elementary expression. No balance, connectivity, saturation or recurrence
hypothesis remains. All finite alphabets, including m=0, are covered. Circular
`Diagram n` requires n>0; an empty-vertex component is not represented here.
The formal statement is finite strict/e, corresponding to the manuscript's
weak/h convention; a finite-alphabet omega translation is not claimed.
The original ordinary and aggregate circular LLT theorems remain complete.

## Verification

Current full library: **2074 jobs**. Current axiom inventory: **2803 entries**, only
`propext`, `Classical.choice` and `Quot.sound`. No placeholders, custom axioms
or unchecked native proofs. Source guards, edited modules' 100-column checks,
public-header preservation and `git diff --check` pass. Existing linter/deprecation warnings remain.
Pinned Lean 4.34.0 / Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

Current streamlining logs: `streamlining-audit/library-build.log` and
`streamlining-audit/axioms.log` under the project request cache. Original completion
logs under `/lake-cache/ai-projects/requests/VerticalStripLLT/circular-continuation/`:

- `hrv-scan-extraction-build.log`: Claude candidate, first local build passes.
- `component-positive-build.log`: Luna positivity candidate passes.
- `component-expansion-build.log`: ordinary and circular assembly, 1776 jobs.
- `component-completion-library-build.log`: full library, 2074 jobs.
- `component-completion-axioms.log`: 2800 entries, standard axioms only.

Independent Astra audit found no semantic defect in the final extraction,
ordinary assembly, circular transport or public weighted/positivity statements.

## Ownership and workflow

Academic restart retained `/workspace/lean/VerticalStripLLT`, branch `main`.
Primary owns all integrated source, docs and the sole serialized Lean build slot.
No auxiliary build or implementation process remains active. All Astra/Luna
assignments are released. The explicitly authorized nested Claude consultant
completed normally. The implementation consultant edited only
`Components/HRVScanExtraction.lean`; the later streamlining consultant was
read-only. Primary locally verified all integrated candidates.
No new account, worktree or supervisor worker was started.

Before any future build, inspect Lean/Lake processes across all projects.
Use `lake-workspace`, never plain Lake. All artifacts remain under `/lake-cache`.
Runtime Lean MCP is rooted in RealRooted; the recorded fallback is source search
and serialized wrapper builds (`suggestions/project-tool-routing.md`). Runtime
registry and `codex mcp list` were inspected during this continuation.

Routine pushes use existing gh credentials without changing remote configuration:

```sh
git -c url.https://github.com/.insteadOf=git@github.com: \
  -c credential.helper='!gh auth git-credential' push origin main
```

## Checkpoints and recovery

Implementation checkpoint **`f355a28`** completes the component proof and adds
HRVScanExtraction, ComponentPositive, OrdinaryComponentExpansion and
ComponentExpansion. Preceding pushed checkpoints:

- `8af13f9`: actual component scan semantics and cancellation, 2070/2784.
- `d0244d7`: complete conditional circular-to-ordinary reduction, 2060/2743.
- `33cdecc`: whole-component undecoration and normalized lifts, 2041/2627.
- `0eac2b2`: coefficient constancy, 2033/2590.
- `d4af8ce`: tight flip reconstruction, 2029/2578.
- `6bf5f42`: actual finite companion, 2017/2529.

Detailed earlier progress is archived in
[the balanced-reduction handoff](docs/archive/component-foundation-through-balanced-reduction-20260927.md)
and [the scan handoff](docs/archive/component-scan-handoff-20260927.md).
The accepted shorter route needs only forward flip transport: the compatible
ordinary preimage is a union of complete components. Direct HRV threshold
induction replaces a global ordered-partition bijection.
No further Lean proof work is queued. Cumulant formalization and a general
symmetric-functions library remain outside the completed formalization task.
The subsequent user-authorized manuscript rewrite is recorded above.

## Post-completion cleanup

User requested conservative proof golf, notes consolidation, a short presentable
README and a challenge file. Primary owns all source and the sole build slot;
Luna's bounded MountainScan assignment is returned and released.

- MountainScan: function extensionality replaces recursive congruence; scalar
  linearity uses direct finite-sum simplification. 110 to 94 lines.
- HRVScanExtraction: shorter cutoff and conditional cases, direct full-cutoff
  specialization, current if/Fin lemma names. 259 to 234 lines.
- All public theorem headers and hypotheses are unchanged. These two modules
  compile without warnings; no runtime speedup is claimed from shorter source.
- README: 129 to 43 lines. docs/README: 128 to 29 lines; the detailed catalogue
  is retained in docs/RESEARCH_NOTES.md. Earlier research notes now carry explicit
  historical labels, and stale completion claims in the source audit and ledger
  are corrected without promoting unused auxiliary claims to theorems.
- Challenge.lean states faithful ordinary/circular targets using semantic imports
  only. CHALLENGE.md gives constraints, smaller targets and checking instructions.
  It is a project-based challenge, not a self-contained Mathlib-only export.
- Independent Astra review found no issue with the proof edits or challenge.

Cleanup full build: 2074 jobs; inventory: 2800 entries, only the standard axioms.
Logs: `/lake-cache/ai-projects/requests/VerticalStripLLT/post-completion-cleanup/`.
Challenge.lean compiles, and the separate ChallengeReference.lean check confirms
both challenge propositions match the proved theorems (standard axioms only).
Source widths, unchanged public headers, relative documentation links and
`git diff --check` pass. Baseline: 23d4df7; proof checkpoint: f355a28.
Proof-cleanup checkpoint: `7e9e31b`. The accompanying documentation checkpoint
adds Challenge.lean/CHALLENGE.md, the short README and the organized research
catalogue. All cleanup assignments are released; no owned process remains active.

## Second streamlining pass: complete

User requested further proof golf, useful shared lemmas and a Claude audit.
Verified implementation checkpoint: **`0b64954`**, on `main`, based on `a8fdacd`.
Primary owned all 13 edited component modules,
Verification.lean and accompanying documentation. No account, worktree or
supervisor worker changed. All implementation and review assignments are released.

The read-only Claude audit completed normally (20-minute monitored cap,
Read/Glob/Grep only, no compiler or write access). Primary implemented its five
recommendations plus circular grouping simplifications. Independent Astra review
found no semantic or public-signature regression. See
[the streamlining audit](docs/PROOF_STREAMLINING.md) for decisions and reusable
helpers. Source length falls from 1845 to 1731 lines across 13 modules; every
existing public header is preserved. The helpers have two, two and six uses.

All edited modules passed focused builds, followed by the full 2074-job build
and 2803-entry axiom inventory (standard axioms only). The tail wrapper requires
an explicit expanded carrier-predicate hypothesis to simplify both conditionals;
the cancellation rewrite requires an explicit summand. Source guards, 100-column
checks, documentation links and diff checks pass. No runtime speedup is claimed.

Logs: `/lake-cache/ai-projects/requests/VerticalStripLLT/streamlining-audit/`:
`claude-audit-result.md`, `component-grouping-build.log`,
`claude-recommendations-build-5.log`, `library-build.log`, `axioms.log`.
Builds were serialized around the other project's work. All owned compiler,
consultant and wait processes finished. No further cleanup is queued.
