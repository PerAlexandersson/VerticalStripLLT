# VerticalStripLLT handoff

## Current four-cycle attachment checkpoint

2026-09-28, continuation from clean pushed `37e813a`. Previous goal turn
made proved progress. The full recurrence/diamond proof remains open;
the new theorem resolves one complete NN generator in cycle rank one.

New [four-cycle swap theorem](docs/proofs/COMPONENT_FOUR_CYCLE_SWAP.md):
for eligible saturated ordinary NN a<b=a+1<c, any connected unicyclic
state containing {ac,ad,bd,bc}, b<d<c, is connected by actual flips to
its adjacent-swap image, with arbitrary attached trees. This proves the
RIGHT second mixed NN join stays in one source component.

Proof ingredients: a six-flip incoming-attachment transfer using a strict
corner in another branch; seven flips move the interior cycle vertex along
an attached edge. A new [tree interval-path lemma](docs/proofs/COMPONENT_TREE_CONNECTIVITY.md)
normalizes the containing corner's branch so its path to the core stays
inside the endpoint interval. Move the cycle along that path, transfer
the incoming branch, then undo migration and normalization. The moved
branch remains pendant and cannot alter the reversed cover tests.
Strict edges are retained. Same-branch shields use tree connectivity and
a conjugated return path. Primary and independent Astra audited the final
written proof and every local cover test, including empty-path cases.

Exact checks: six-/seven-flip tables; all 149 relevant unicyclic states in
all 76 eligible NN instances through n=6; another 44 and 13 states in
two n=7 fixtures. All adjacent-swap images lie in the same actual component.
A separate exact K5 counterexample shows that keeping a normal edge
redundant throughout a tree-normalizing path is too strong, even for the
special pair and the same directed path. Do not use that rejected shortcut.

The unicyclic note also records two partial skipped-b reductions: q=1
paths lift under A→A−q+r, and first-mixed incidences correspond to actual
q-changing flips inside the inactive component. Comparing their exterior
swaps and propagating across whole q=0 excursions remain unproved.

Receipts, frozen sources/manifest/lock, commands and 17 hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/four-cycle-attachment/`.
All final jobs finished exit 0. Primary owns notes/index/handoff and
external consumer, retaining the sole Lean build slot. Existing Astra
simpler_component_route supplied independent proofs/audits and the precise
restricted-tree obstruction; all bounded assignments are finished.
Independent proof audit, exact checks, frozen hashes, local documentation
links and `git diff --check` pass. No delegated edits or owned live processes.
No new worker/account, Claude
call, Lean build, manuscript edit or maintained Rust source edit.
Runtime/MCP and Rust capabilities refreshed; Lean MCP still targets the
other project. Existing flip-enumeration integration proposal remains.

Next: LEFT second mixed NN join; middle/first-mixed joins between surviving
components; skipped-b inactive-f neighbor uniqueness including q=0 pieces.
Higher cycle ranks, DN/DD isolation, and recurrence coverage remain part of
the full goal. The completed word proof is not a substitute for this task.

## Current unicyclic packet checkpoint

2026-09-28, continuation from clean pushed `148cc9c`; previous goal turn
made proved progress. The general recurrence/diamond component proof is
still incomplete. Keep the full goal active and preserve the manuscript.

New results in [the unicyclic note](docs/proofs/COMPONENT_UNICYCLIC_REDUNDANCY.md):

- A connected unicyclic component is wholly mixed-cyclic exactly when one
  strict corner is redundant throughout. A mixed directed cycle with two
  strict edges has an actual flip breaking it; the no-switch lemma handles
  the one-strict-edge case. Thus all discarded components are classified
  by insertion into whole tree components with a forced maximal chain.
- Across NN joins, inactivity at g different from the distinguished corner
  f is preserved. The forced chain avoids the adjacent vertices a,b and
  remains maximal under the swap. LEFT mixed joins also change ta outside
  f; the common selected long tb shields it. This detail is incorporated
  following the independent audit. Such vertices cannot lead to a survivor.
- An inactive-f bypass a→b→c gives an isolated packet vertex. A longer
  bypass through b gives exactly one neighboring component, which survives.
  The entire middle image is connected by lifted actual flips.
- A nine-vertex exact example joins DISTINCT inactive-g components (g≠f).
  Different deletion envelopes prove they are different whole components.
  Do not strengthen label preservation to equality of components.

Exact scan: all 76 eligible NN instances through n=6, 99 connected
unicyclic component occurrences (22 surviving, 77 inactive). The common
strict-corner classification and proved NN predicates pass. Distinguished
inactive bypass counts: 27 skip b, 22 have length two through b, 19 are
longer through b. All 46 distinct intercomponent joins in this bounded
scan go from inactive-f to surviving; this is NOT a uniform theorem.
The two n=7 fixtures pass too. The n=9 example is checked locally,
without enumerating its entire state space; the structural tree theorem
supplies the whole-component and distinctness conclusions.

Frozen sources, manifest/lock, receipts/logs, commands and 13 hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/unicyclic-packet/`.
All final jobs finished exit 0. Primary owns the notes/index/handoff and
external consumer, retaining the sole Lean build slot. Existing Astra
simpler_component_route supplied the classification and through-b cases,
audited the other-corner proof, and independently checked the n=9 example.
All bounded assignments are finished, no delegated edits or live jobs.
Independent mathematical audit, exact assertions, frozen-file hashes,
relative documentation links and `git diff --check` pass.
No new worker/account, Claude call, Lean build, manuscript edit or shared
Rust source edit. Registry/MCP and Rust capabilities refreshed; Lean MCP
still targets RealRooted. Existing flip-enumeration API proposal remains.

Next: control the inactive-f forced chain that skips b, and prove source
connectivity for surviving-to-surviving joins. A right second mixed join
contains an alternating four-cycle with attached exterior trees; outgoing
branches can be swapped by two actual flips. Incoming branches can be
shielded by a strict edge in a DIFFERENT branch, so tree connectivity
inside one branch does not prove the general swap. Higher cycle ranks,
DN/DD isolation and complete recurrence coverage remain necessary too.

## Current global-reassembly checkpoint

2026-09-28, continuation from clean pushed `246345c`. The requested general
recurrence/diamond component proof is still incomplete; the earlier full
Lean word/finite-companion proof remains complete. Keep the research goal
active. No manuscript or Lean theorem has been replaced by this partial route.

New [whole-component correction](docs/proofs/COMPONENT_GLOBAL_REASSEMBLY.md):
for NN at 26 in area (0,1,2,3,4,3,4), strict corners 04,26, the remaining 1693-state component
has a packet consisting of itself plus an inactive 89-state component.
The packet transports to 26 whole smaller components, total 1,782 states;
deleting 26 from the correction gives one whole 89-state tree component.
Thus this particular source component has the same signed recurrence for
K/E. Finite packet identification is exhaustive, not a general theorem.
All 1,405 source components give 703 packets; each has at most one of the six
remaining components. All 55,232 directed target flips preserve packet weights.

New uniform theorem in [tree connectivity](docs/proofs/COMPONENT_TREE_CONNECTIVITY.md):
reachability common to all trees with envelope H is exactly Reach(M), where
M is its maximal intervals. Contract the increasing chains of M, prove the
quotient strongly connected, and extend a reverse quotient path to a tree.
It characterizes inactive strict-corner insertions into tree components.
Primary and independent Astra audited both proofs; exact enumeration agrees
for 1,441 trees in 64 whole components, n=2..6.

The same 1,693-state example disproves endpoint-only redundant-edge repair:
the canonical NN weights differ across an actual flip between two TREES.
Both selected-edge lists and the safe whole-component correction are in
the note. Do not infer that every bad boundary has a redundant endpoint.

Receipts, frozen source/manifest/lock, reproduction commands and 20 hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/global-reassembly/`.
All mathematical computation jobs finished exit 0, including the final
26-target-list and 89-state deletion check. No new polynomial family or
maintained Rust edit; existing flip API integration proposal remains.

Primary owns notes/index/handoff/external consumers and sole Lean build slot.
Existing Astra simpler_component_route worked read-only/build-free and its
bounded final audit is complete. No delegated edits or active Rust jobs.
The authorized read-only Claude global-construction consultation reached
its 20-minute timeout (exit 124, session 75994 terminal), without final text
or a result record. No Claude proof or audit conclusion is adopted. Request,
stream and status are retained externally. No account/model override or new worker.
Registry/MCP and Rust capability checks refreshed. No Lean build occurred.
All owned processes are terminal; exact Claude PIDs and descendants are absent.
Independent proof audit, frozen receipt hashes, documentation links and
`git diff --check` pass.

Next: prove general whole-component reconstruction. The remaining packet question is whether
paths through solved source components can join two distinct surviving
components. The new tree theorem does not establish that isolation claim.

## Earlier recurrence research

[Archived checkpoints](docs/archive/component-recurrence-handoff-through-redundancy-20260928.md)
retain the NN/DN/DD packet proofs, exact failures of stronger isolation
claims, direct local reconstructions, and redundancy-diamond results.
The latest preceding checkpoint is `246345c`, pushed to `origin/main`.
The current proof notes are indexed by [docs/README.md](docs/README.md).

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
