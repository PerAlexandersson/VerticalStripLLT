# VerticalStripLLT handoff

## Active recurrence continuation

2026-09-28, latest user steering: work directly with the existing diagrams.
Split ONE component by each decreasing recurrence, redistribute with diamonds,
and collect whole smaller components with the same expression for colorings.
Use Rust to study the details. Do not impose packet isolation as a necessary
condition. Primary owns the proof notes/index/handoff and the external Rust
probe; no shared Rust source, Lean source, or manuscript edits. No Lean build.

New [direct NN note](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md) proves the
initial split for any component, retaining unmatched middle states in the
corner-deletion diagram. Its five-orientation example has a short hand proof
using one source diamond and two smaller-diagram diamonds:
`X(C)=X(D1)+X(D2)+X(D3)-X(D4)`, simultaneously for K/E. Astra supplied and
audited the construction; Luna confirmed the local split after clarifying
that unweighted state valuations ignore strict/normal marking.

Rust reused the existing bounded cover-flip model, maintained exact linear
algebra, strict P-partition enumeration and HRV APIs. It found direct integral
expressions for all components of three selected diagrams (3,15,18 components)
and three selected six-vertex components. Four further six-vertex components
required additional target diamonds, equal transitive closures and safe
adjacent relabelings; these have exact rational certificates, hence integral
certificates after clearing denominators. Every expression was independently
checked on BOTH symbolic valuations. This is finite evidence and one short
worked proof, not a uniform reconstruction theorem. The next task is to turn
the successful diagram redistributions into a general case argument, then
handle the other decreasing recurrences. Auxiliary J isolation is optional.

Also proved: NN packets preserve weak blocks and edge counts; ordinary DD
packet transport follows from exact selected/unselected corner sectors.
The common ordinary measure is `(vertices, raw area sum, area moment)`,
which handles DD even when doubled decorated area increases. Both Astra
and Luna audited DD; all 44 eligible saturated DD instances through seven
vertices passed the refined finite isolation test. See
`docs/proofs/COMPONENT_DD_PACKETS.md`. Circular transport remains open.

External receipt directory: `recurrence-continuation/`; principal Rust receipt
`nn_rust_transport_certificates.jsonl`. Source is
`diamond-exploration/hrv-bridge/src/bin/nn_component_transport.rs`, reusing
`component_source_probe.rs` (only crate visibility was widened there; prior
text preserved). Hashes are in `SHA256SUMS.json`. All jobs and both existing
read-only/build-free agent assignments finished. No new workers/accounts or
Claude calls. Primary retains the sole serialized Lean build slot.

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
