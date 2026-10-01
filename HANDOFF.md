# VerticalStripLLT handoff

## Active split — Claude owns Lean; Codex owns the writeup

Ownership transfer recorded 2026-10-01, after the two pending P6 modules
passed focused builds and all 649 axiom checks. The persistent Claude worker
`agent-verticalstri-motzki-c-001af720` may now take all `DiagramProof/` Lean
implementation, `DiagramProofVerification.lean`, and the **sole project build
slot**. Begin with issue #8 and continue the remaining diagram formalization.
Serialize builds with other Lean projects. Codex and its subagents will run
no further Lean builds or edit Lean sources after this release.

Codex retains `HANDOFF.md`, mathematical proof prose, formalization source maps,
`docs/drafts/`, figures and manuscript work. Claude should report durable status,
checks, commits and needed proof clarifications in `docs/LEAN_COORDINATION.md`
(new file owned by Claude); Codex will incorporate those reports here.
This transfer releases all earlier Codex source ownership below. All delegated
source tasks have returned. At the transfer, Codex had no compiler or queued
build remaining; Claude now runs its own focused checks.

The Docker-side supervisor report/tail did not discover the persistent session;
a read-only tmux inspection confirmed Claude was preparing attachment files in
its scratchpad and waiting for this explicit transfer. No input guards were
bypassed. This paragraph is the durable release the worker was instructed to read.

P0–P5 are complete under their contracts. Claude reports the no-articulation
P6 induction checked at `fb68ff5`. Its initial-path extension was committed
as `58b8b4b`; the focused build passed, and its axiom audit is not yet recorded.
P7/P8/P10 are open,
and P9 has its attachment lemma checked; prefix and first-drop coverage remain.
The complete mathematical diagram proof and the independent Lean theorem
remain distinct. The older word/scan proof is not imported by this route.

### Writing progress after the transfer

Source/build release is pushed as `b78312c`. Claude's attachment checkpoint
`26b2d97` is now pushed. The four `RightAttachment*.lean` modules give the
actual union/cut constructions, exact whole product component, HRV fibre
merger, endpoint-omitted K/E gluing, paired integer recurrence transfer, and
area/moment decrease. No identity for the attached component is assumed.
This completes issue #8's attachment subtask, not P9 or the full theorem.

The writer inspected the public source, the focused successful build log and
all 719 axiom outputs against the current queries in exact order. Only standard
axioms occur. A separate read-only review approved the statement, whole-component
scope, actual HRV semantics and conditional transfer. Claude's durable report
is [LEAN_COORDINATION](docs/LEAN_COORDINATION.md); it owns that file and continues
P6. Its coefficient form `z i • V` over `ℤ` and lexicographic `(area,moment)`
for fixed-size prefixes match the written recurrence and plan.

Writing checkpoint `52afc77` is pushed. Issue #8 was read back and matches
the tracked task after conversion of relative links to repository links.
The new circular section `docs/drafts/CIRCULAR_E_EXPANSION.md` follows the
checked aggregate proof. It separately treats the terminal-contact reduction
(factor `1+q`, doubled area down six) and interior column reversal; the
external manuscript had grouped their geometry. The rank definition is the
sum of proper-ancestor counts times strict-edge lengths, exactly Lean's
`strictRank`. A new column-reversal SVG was rendered in the external cache
and visually inspected. The local boundary checks and DD-contact elimination
remain compressed, and the combined manuscript remains unfinished.
Independent review approved the terminal-pair count, both contact branches,
and the exact rank definition. Local Markdown links and SVG XML pass; issue
#8 was refreshed to match the tracked task.

### P6 interfaces and subsequent induction

`lastClique_induced_short_naturalEdges` in `LastCliqueNaturalEdges` preserves
short natural edges in the canonical core on `0,...,c,e`; interior pairs
lift identically, and final pairs lie inside the given crossing edge.
`CornerFamily.commonCover_connected_of_terminal_card_le_two` derives the
existing two-terminal base from the bound on terminal fixed points.
Terra supplied the former and Luna the latter; Codex repaired and verified
both. These were auxiliary lemmas for the subsequent global induction below.

Checks: 649 axiom queries in exact order, only standard axioms; independent
closure 283 project files; 209 DiagramProof modules pass source/100-column
guards. Logs in the external request directory: `p6-core-short-build.log`,
`p6-two-chain-card-build.log`, `p6-core-geometry-axioms.log`, and
`p6-core-geometry-imports.txt`. No broad build or dependency update ran.

Claude completed the no-articulation integration in `fb68ff5` after this
earlier P6 checkpoint: `commonCoverUnique_of_shortEdges` assembles strong
induction with the complete-diagram bridge and reversed first-clique branch.
Its coordination note reports 724 passing standard-axiom checks. Codex has
not rerun those checks and retains no build ownership. Claude subsequently
implemented `commonCoverUnique_of_initialPathBlock` at `58b8b4b`. Codex read
`claude-right-attachment/logs/initpath-2.log`: the focused build passed, with
one unused-simp warning. Its new queries are not yet in
`DiagramProofVerification.lean`, so the earlier 724-query report does not
cover this extension. Claude continues to own verification and its next P7 work.

## Current writing increment

The user explicitly requested general figure macros whose diagrams denote sums
of all objects satisfying the pictured restrictions. `docs/drafts/tex/llt-diagrams.sty`
now supplies this convention: arbitrary ordered labels, optional/selected/absent/
forbidden/strict cells, cover restrictions, global conditions, and weighted or
unweighted sums. A two-page illustrated guide and small diamond and layer
figures compile in the external `diagram-formalization/tex-preview/` directory.
All three PDFs were visually inspected; no TeX warnings or box warnings occur.
The diamond and NN/DN layer SVGs are generated from those macro sources.
No external Overleaf files were edited.

The ordinary draft now gives the full HRV-map diamond proof, the three
whole-component corrections, selected-envelope normalization and the refined
NN/DN layer calculation. The NN size split is `s,s-1`; DN keeps size `s`. Independent review
approved the diamond, whole-component corrections and layer calculation;
its requests to spell out exterior disjointness, strict decorations and the
original shifted normal-edge exponent were incorporated.
The diagrams themselves denote sums with the selected-edge count shown below.
Complete/two-chain bases, last-clique inheritance, and the chain-quotient
lemma still need detailed manuscript proofs. The final first-drop/prefix
induction is now expanded:
articulation test, first nontrivial prefix, strict-corner preservation, all
four contact cases, marking changes, area/moment decrease and final induction.
The new prefix-attachment figure uses restricted sums with a fixed endpoint
color and an omitted shared-vertex weight. `\LLTAreaDiagram` generates the
forbidden cells directly from ordinary area data and checks the area bounds.
The figure compiled without TeX or box warnings and was visually inspected.
Independent read-only review found no new flaw in prefix selection or the
final induction. Its clarifications about local area indexing, the new DN
edge and the retained unmarked corner were incorporated. Local Markdown links,
SVG XML, exact rendered-source correspondence and `git diff --check` pass.

Writing checkpoint `5014939` is pushed. The next writing increment supplies
full preparation and crossing-slide proofs: process chains in decreasing
terminal order, recover all corner covers after each chain, sweep both
obstructions, perform the two central flips, then restore right before left.
That restoration order agrees with `exists_crossingSlide`; the historical
research note uses the other valid order and remains unchanged. The new
four-state figure records all six actual flips and fixes every natural cell.
The preparation statement follows the checked existence/retention interface;
it does not add an unformalized exact endpoint formula.
Independent read-only review approved both new proofs and the exact four
displayed states. The figure compiled without TeX or box warnings and was
visually inspected; local links, SVG XML and exact source correspondence pass.
Claude's source-only checkpoint `cdac9cc` appeared during this writing pass,
adding relational transport and extracting the measures. Its ongoing Lean
edits remain Claude-owned and are excluded from this writing checkpoint.
The circular section and combined manuscript have the remaining limits already
recorded above. The full user goal is unchanged and unfinished.

## Sources, verification and recovery

Primary mathematical sources are
[the assembled diagram proof](docs/proofs/COMPONENT_DIAGRAM_COMPLETION.md),
[its cleanup audit](docs/proofs/COMPONENT_DIAGRAM_AUDIT.md),
[the formalization plan](docs/COMPONENT_DIAGRAM_FORMALIZATION_PLAN.md), and
[the draft correspondence](docs/drafts/README.md).
The invoked writing skill is
[combinatorics-paper-writing](/home/dev/.codex/skills/combinatorics-paper-writing/SKILL.md).
Keep mathematical prose in first person plural and preserve the author's
cell-diagram conventions. Status and compiler details belong outside the paper.

External request directory:
`/lake-cache/ai-projects/requests/VerticalStripLLT/diagram-formalization/`.
Lean diagnostics use focused `lake-workspace` commands because the Lean MCP
is rooted at RealRooted. Aristotle is available by CLI; no remote request or
watcher owned by Codex is active. Claude owns its own builds and watchers.
No mathematical computation or shared Rust edit was part of this writing pass.

The [complete snapshot through 79ec1d2](docs/archive/diagram-implementation-through-two-chain-base.md)
preserves the preceding implementation record, historical ownership, exact
verification scopes and recovery hashes. It in turn links the older archive.
Historical proof-note prefixes and unrelated ownership remain unchanged;
Codex retains the authorized proof prose and append-only continuations.
Preserve their prefixes at `a3d076b`. Never absorb Claude's dirty Lean source
or its claim/progress notes into a writing checkpoint.
