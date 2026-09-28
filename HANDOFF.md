# VerticalStripLLT handoff

## Active continuation: local diagrams for component recurrences

Latest author steering: the earlier argument used smarter local operations
than the cycle-rank subdivision. Re-read the archived original main.tex
recurrence sketches and the direct NN/DN residual identities. The next step
is DIRECT transport of one component, with target and deletion terms repaired
together by diamonds. Do not impose source balance, packet isolation, or a
cycle-rank induction as an extra goal requirement. The conditional balanced
five-vertex theorem remains useful when applicable; it does not supersede
the unrestricted direct residual identity. The new final section of
COMPONENT_LOCAL_DIAGRAMS.md records this distinction and the general
corner-deletion/inclusion--exclusion reduction. No manuscript edits this turn.

Primary added the DN middle-flip lift and conditional five-vertex proposition
to the local diagram note. Existing Astra reviewer independently checked both
lifts and the full reduction, with arbitrary exterior and cycle rank.
For component-constant balanced h, every target coefficient comparison is
settled except retained-ux or wx-changing flips; these use at most five
vertices together with the recurrence. Constructing the balanced correction
and proving these remaining comparisons are still open in general.
User also requests the same cell diagrams for the circular HRV proof, following
the Robin paper. Primary owns the small figure-only changes to Overleaf
`LLT flip/proof-diagrams.tex`, `dyck-first/diagrams.tex`, the bounce caption
and triangle notation in `dyck-first/circular.tex`, README, map and preview.
Previous files and PDF are copied to the external local-diagram-style receipt.
The shared LLTCells/LLTSelectionTriangle macros now draw the circular bounce,
circular triangle identity and ordinary diamond in the Robin paper's style.
The 13-page preview builds without warnings/box errors and pages4/9 were
visually inspected. No other manuscript proof change or Lean build.
Final written Astra audit passed after clarifying that disjoint commuting
flips can have a seven-vertex raw union; the exceptional bound stays five.
Sources, before/after hashes, review and compile receipts are in
`/lake-cache/ai-projects/requests/VerticalStripLLT/local-diagram-style/`.

From clean pushed `0ff5980`; previous goal turn made verified progress.
Primary owns notes/index/handoff and external-consumer additions. Existing
Astra reviewer completed the read-only DN/coverage audit and released its task.
No new worker/account, Claude child, Lean or manuscript build. Runtime
registry/MCP and Rust capabilities rechecked before bounded probes.

Latest user direction: organize the recurrence/flip overlaps as diagrams,
probably on five vertices, using the same cell notation for circular HRV. The
[local diagram note](docs/proofs/COMPONENT_LOCAL_DIAGRAMS.md) records the
proved two four-vertex NN overlap types. Every DN flip changing its local
(p,q) sector uses at most five vertices together with the recurrence.
The new arbitrary-exterior lifting argument settles the commuting cases
after source balance. Do not claim that five isolated vertices prove the
remaining comparison identities. Next examine the retained-ux overlap
u<t<w<x<z and the wx-changing overlaps, retaining the full exterior.

Previous DN scan finished with exit zero: 111 eligible saturated instances
through seven vertices, 31 all-active connected unicyclic component reports,
no bad middle joins or remaining target/deletion coefficient defects.
These are finite evidence only. Consumer:
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/src/bin/dn_component_transport.rs`;
receipts `dn-direct-rank-one/scan.jsonl` and `scan.log` in the same requests root.
The optional exact valuation mode has not been run. Independent reviewer
confirmed the direct DN formulas for beta=h10; uniform DN repair remains open.

Coverage audit: NN/DN/DD/ND together cover saturated ordinary non-chain
diagrams by choosing the least strict area drop of height at least two
(with terminal sentinel area zero). NN/DN/DD alone do not: area012333 has
only the eligible ND corner25. DD/ND unmarking intermediates need a separate
extension because they are not saturated. Retain this as an induction gap.


## Current component recurrence: the unicyclic NN step is complete

2026-09-28, from clean pushed `f6a5f02`. This turn made verified progress.
The full requested combinatorial proof remains active, ordinary only.
Keep the user's construction central: push ONE component through each
recurrence, repair the pieces, collect complete smaller components with
identical coloring/HRV coefficients.

New [left comparison and NN theorem](docs/proofs/COMPONENT_NN_LEFT_REASSEMBLY.md)
closes the entire connected unicyclic NN step for saturated eligible ordinary
NN diagrams. For C active at every strict corner, the explicit correction
wtilde=w_C+sum_I(w_I−1_DI) is constant on EVERY complete target component
of L-f. Each summand has zero K/E valuation. Consequently
X(C)=sum_D m_D X(D), X=K,E, with the SAME integers m_D and whole smaller
components D. If C is inactive at any strict corner g, delete g to get a
whole tree component. No completed word/component theorem is used.

The new incoming-edge result is carefully scoped. For ta ON the unique
cycle, fr selected and q,tb absent, ta→tb is a component identification
when ta covers initially and tb covers finally. No activity is needed
for this on-cycle theorem. Actual left target flips supply both covers.
Proof: selected-tv base; common tree normalization when t meets a–c–b
at c; paired outgoing flip or swap reduces to a sink at a. If the strict
container lies in the remaining common tree, normalize to select tv.
Otherwise move its branch to a; a pair of local flips either puts it in
that tree or reduces the incoming tail x<t. All new covers are proved.

For a BRIDGE ta, a covering strict container uses earlier bridge lemmas.
If its strict container g is redundant but active, delete g and use two
tree envelopes H⊆H′. F=max(H)+fr+ta and F′=F−ta+tb have the same partition
and contain their respective envelope maxima. A common reverse quotient
path gives two exposed trees, with g covering in BOTH. Separate tree paths
lift upon reinserting maximal g. Exposure may put ta on the cycle: the
new on-cycle theorem handles it. This closes the bridge case for components
active at all strict corners, and hence the left coefficient comparison.
The inactive-f/other-inactive cases use the already proved indicator rules.

Remaining: higher cycle ranks, DN/DD reassembly and general recurrence
coverage. The new result proves a full NN step at cycle rank one, not the
full requested component HRV proof. Next examine the component images of
DN/DD and the hypotheses needed to propagate through subsequent diagrams.
Do not silently assume that all resulting diagrams or components remain
in the saturated connected setting without the existing reductions.

Final checks all passed: all76 eligible NN instances through six vertices
with93 left/511 right comparisons,8396 middle/33584 state checks; the
seven-vertex area0123434 at corner26 adds217 left/216 right comparisons,
16384 middle/65536 state checks. Every full target component has constant
repaired weight for each all-strict-active connected unicyclic source.
Exact bridge-exposure fixture: separate1- and5-flip tree paths,2 and64
local/full cover checks, then a4-flip on-cycle transfer. An8-vertex fixture
checks the actual reduction of tail2 to0 and both new endpoint covers;
its preparatory bridge and terminal selected-interval paths each have4
actual flips. All Rust jobs exited zero and are terminal. No Lean build
or manuscript change; this new proof is not claimed Lean-formalized.

Primary retains note/index/handoff/archive and existing external-consumer
ownership, plus the sole serialized Lean build slot. Existing Astra reviewer
independently audited the construction and final written note, checked no
circular dependency, and released ownership. One citation clarification was
applied (use the older cycle-uses-fr bridge corollary in that branch).
No outstanding correction, new worker, account change or Claude child.

Runtime registry, codex mcp list, Rust guide/metadata/source APIs inspected.
Lean MCP remains rooted in RealRooted and unused. Maintained Rust HEAD:
`d53fb193af3c69adedbd9ec8592f87235d809ffa`; shared graph/flip APIs reused,
no maintained Rust edits or polynomial generator. Python only processed
files, summaries and hashes. Writing-guide skill followed for the proof note.
Frozen source, exact commands, receipts, independent audit and checked hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/nn-left-transfer/`.
The restricted simultaneous-preparation search in exploratory receipts fails
on one bridge example; the proved separate tree paths resolve that example.

[Archived checkpoints](docs/archive/component-recurrence-handoff-through-path-square-20260928.md)
retain `f6a5f02` (full active swap/right comparison), `50268ce` (whole-tree
correction), and preceding increments. Current note links supersede the
old remaining-left statements within their stated scope.

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
