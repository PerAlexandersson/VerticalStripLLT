# VerticalStripLLT handoff

## Current unicyclic block checkpoint

2026-09-28, continuation from clean pushed `cd29b7a`. The preceding goal
turn made proved progress. This increment adds a structural lemma, a
checked local repair, and exhaustive evidence; it does not complete the
requested general recurrence/diamond proof.

New [unicyclic block note](docs/proofs/COMPONENT_UNICYCLIC_BLOCKS.md):
contracting strict chains in an articulation-free ordinary natural graph
creates no loops or articulation. Deleting one chain leaves consecutive
labels at distance at most two, hence connected. The two-vertex multigraph
case has parallel edges and is handled explicitly.

The stronger uniqueness question remains open: is there at most one
surviving connected unicyclic component in each natural block? Exact search
passes every articulation-free saturated diagram on7 and8 vertices:
42/132 graphs,59881/1280832 connected selected states, one survivor per graph.
All survivors also contain a leaf-at-0 state with the full remaining
natural envelope. These finite assertions do not prove either uniform claim.
The known two-K4 articulation counterexample excludes unrestricted uniqueness.

Two precise obstructions guide the next proof attempt. Contracting the
smallest cycle vertex can create a redundant strict edge before reaching
a triangle. Also the tree envelope-augmentation sweep can make its retained
corner redundant halfway through. A five-flip repair fixes the smallest
K5 example and restores the smaller envelope. Primary and existing Astra
independently audited the lemma, examples, repair and final written note.
A full-envelope smaller component may still be inactive (explicit n4
example), so an induction must retain its correction rather than discard it.

Frozen sources/model, Cargo files, commands, receipts and18 hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/unicyclic-blocks/`.
Final n7/n8 scans and repair finished exit0. An initial n8 run reached its
200000-state BFS cap only at K8; a bounded1m-cap rerun completed it and the
final full scan. A compile-only reference-pattern typo was fixed before
leaf-test execution. Historical logs are labeled; neither error is a
mathematical counterexample. Documentation links, hashes and diff checks pass.

Primary owns notes/index/handoff and the external consumer; sole serialized
Lean build slot retained. Astra's bounded read-only assignments are finished,
and all owned processes are terminal. No new workers/accounts, Claude call,
Lean build, manuscript edit or maintained Rust edit. Runtime/MCP and Rust
capabilities refreshed; Lean MCP still targets RealRooted and was unused.
Existing flip-enumeration API integration proposal remains.

Next: find a uniform repair that restores the smaller envelope after corner
leaf normalization, or close the remaining first/middle NN joins directly.
The unicyclic block evidence is a possible isolation route, not a replacement
for the full goal: higher cycle ranks, DN/DD and recurrence coverage remain.

## Current unicyclic swap checkpoint

2026-09-28, continuation from clean pushed `47a9c13`. This goal turn made
proved progress. The full recurrence/diamond component proof remains open;
the completed Lean word proof is not a substitute for the requested route.

[The four-cycle note](docs/proofs/COMPONENT_FOUR_CYCLE_SWAP.md) now proves
both LEFT and RIGHT second mixed NN joins stay in one connected unicyclic
source component. The left proof converts to the right core by two flips,
uses the earlier strict-corner attachment transfer, and undoes the temporary
moves. Arbitrary attached trees and all original strict corners are retained.

New general theorem: if a connected unicyclic state contains f=ac,r=bc,
omits q=ab, and its cycle contains either f or r, it is connected by actual
flips to its full adjacent-swap image. Delete f (or first swap if needed).
The tree envelope has r maximal; adjoining q to its maximal chains is a
forest. Normalize toward a tree containing q, stop before its first
introduction, apply the resulting four-cycle swap, and reverse the swapped
prefix. This avoids normalizing any q-containing state by conjugation.

Every nonactual middle join has a σ-invariant 01 endpoint. This does NOT
connect it to the 10 endpoint. A first mixed join still has an additional
ad/bd or ta/tb attachment discrepancy after the swap; the note displays it.
Middle/first mixed joins between surviving components, skipped-b inactive-f
neighbor uniqueness across q=0 pieces, higher cycle ranks, DN/DD isolation,
and full recurrence coverage remain open. No manuscript replacement.

Checks: left theorem on 24 states in all 76 eligible NN instances through
n=6, plus 47 and 5 in two n=7 fixtures; two explicit conversion tables.
General theorem with f on the cycle on 519 states in the same scan, plus
257 and 72 in the fixtures. All are actual-component assertions, not
polynomial comparisons. Every final Rust command finished exit 0.
Historical manifest-path and missing-natural-edge lookup errors are retained
and identified separately; both were fixed before the successful scans.

Primary and existing Astra simpler_component_route audited the proofs and
final statements. The authorized tool-free Claude audit finished exit 0
(native session 40855) and confirmed the longer normal-form argument,
cover preservation and stopped-prefix conjugation. Primary's shorter
q-forcing argument received its own independent Astra review. No result
is attributed to a reviewer who did not inspect that version.

Frozen consumer/source model, Cargo files, commands, receipts, Claude outcome
and 29 hashes: `/lake-cache/ai-projects/requests/VerticalStripLLT/left-four-cycle/`.
Primary owns the proof notes, docs index, handoff/archive and external
consumer, and retains the sole serialized Lean build slot. All bounded
agent assignments and owned processes are finished. No new worker/account,
Lean build, manuscript edit or maintained Rust edit. Existing flip API
integration proposal remains; Lean MCP still targets RealRooted and was unused.
Mathematical audits, finite assertions, documentation links, frozen receipt
hashes and `git diff --check` are the checks for this checkpoint.

## Earlier recurrence research

[Recent checkpoints](docs/archive/component-recurrence-handoff-through-four-cycle-20260928.md)
retain the right four-cycle, unicyclic classification and global-reassembly
proofs and receipts. [Earlier checkpoints](docs/archive/component-recurrence-handoff-through-redundancy-20260928.md)
retain the NN/DN/DD packet proofs, exact failures of stronger isolation
claims, direct local reconstructions, and redundancy-diamond results.
The latest preceding checkpoint is `cd29b7a`, pushed to `origin/main`.
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
