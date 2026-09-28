# VerticalStripLLT handoff

## Current component recurrence: right NN comparisons proved

2026-09-28, continuation from clean pushed `50268ce`. Verified progress;
the requested combinatorial component-proof goal remains active, ordinary
only. Push ONE component through the recurrences, repair the pieces, and
collect complete smaller components with the same K/E coefficients.

New [active swap proof](docs/proofs/COMPONENT_NN_ACTIVE_SWAP.md): in a
connected unicyclic component active at every strict corner, every state
selecting f=ac,r=bc and omitting q=ab lies in the same component as its
adjacent swap (a b). Activity means covering in SOME component state,
not necessarily in the state under consideration.

The new step exposes a redundant remote strict corner g using a prescribed
forest. Retaining original incident edges alone was insufficient: new
incoming lifts could change the swapped tree envelope. Replacing each bad
new sa by sb fixes both envelopes while preserving the reverse quotient
path. Separate tree-connectivity paths lift after reinserting maximal g.
The existing cycle-position lemmas then complete the swap.

This proves ALL right first comparisons for the corrected unicyclic NN
image, without assuming the target r or source f covers. All-strict-active,
f-inactive, and other-strict-inactive source cases are accounted for.
The preceding [whole-tree correction](docs/proofs/COMPONENT_NN_UNICYCLIC_REASSEMBLY.md)
still gives the entire r-absent sector as complete smaller components and
preserves all q-preserving equalities. Connected selected-r tree sectors,
disconnected target unicycles and target components inactive at r were
already settled.

Remaining at cycle rank one: LEFT first comparisons in selected-r connected
active target unicycles. A sufficient next lemma transfers an incoming ta
to tb in an all-strict-active unicycle while restoring every other edge.
Existing incoming-bridge results cover only part of this claim. Higher
cycle ranks, DN/DD reassembly and general recurrence coverage remain open.
The completed word/component HRV theorem is not used in these arguments.

Verification: all 76 eligible NN instances through six vertices give
951 full swaps and 511 right comparisons; area (0,1,2,3,4,3,4), corner26,
adds 435 swaps and 216 right comparisons. Existing whole-image assertions
also pass. The exact eight-vertex normalized-lift example has two verified
six-flip tree paths (383 and 164 local/full cover comparisons). Independent
whole-component BFS connects all four endpoints in 38,433 states with
107,468 flip edges. These finite checks do not settle the remaining cases.
All three Rust jobs exited zero. No Lean/manuscript change or build.

Primary retains note/index/handoff/archive and external-consumer ownership,
and the sole serialized Lean build slot. Existing Astra reviewer completed
both mathematical and written audits; the lift gap and two scope wording
fixes were resolved, with no outstanding correction. All subagent ownership
is released. No new worker or account was launched.

The authorized nested Claude consultation returned no written answer before
its 1200-second bound (exit124). Exact owned processes are confirmed gone;
no retry or account/model change. It is NOT credited as a successful audit.
Runtime registry, MCP list and Rust capabilities were checked. Lean MCP
still routes to RealRooted and is unused. Maintained Rust HEAD remains
`d53fb193af3c69adedbd9ec8592f87235d809ffa`; existing graph/flip APIs reused,
no maintained Rust edits or polynomial generator. Python only processed
files, summaries and hashes. Existing integration suggestions apply.

Frozen source, receipts, independent audit, consultant terminal status and
checked hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/nn-active-first-joins/`.
[Archived checkpoints](docs/archive/component-recurrence-handoff-through-path-square-20260928.md)
retain the preceding `50268ce` whole-tree correction and earlier increments.

## Earlier recurrence research

[Recent checkpoints](docs/archive/component-recurrence-handoff-through-four-cycle-20260928.md)
retain the right four-cycle, unicyclic classification and global-reassembly
proofs and receipts. [Earlier checkpoints](docs/archive/component-recurrence-handoff-through-redundancy-20260928.md)
retain the NN/DN/DD packet proofs, exact failures of stronger isolation
claims, direct local reconstructions, and redundancy-diamond results.
The tree-sector checkpoint is `756f850`, pushed to `origin/main`.
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
