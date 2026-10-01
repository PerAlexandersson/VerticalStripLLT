# VerticalStripLLT handoff

## Active ownership — Claude owns Lean; Codex owns the writeup

Transfer pushed at `b78312c`, 2026-10-01. Persistent Claude worker
`agent-verticalstri-motzki-c-001af720` owns all `DiagramProof/` Lean sources,
`DiagramProofVerification.lean`, and the **sole Lean build slot**. Serialize
with other Lean projects. Codex and its subagents must not edit Lean or run
Lean builds. Claude owns [LEAN_COORDINATION](docs/LEAN_COORDINATION.md),
whose latest recorded report covers the attachment and no-articulation proofs.

Codex owns this handoff, mathematical prose, formalization maps and plan,
`docs/drafts/`, figures and manuscript work. The three read-only subagents
`semantic_extract`, `anchor_sizes` and `good_edges` have returned the
last-clique writing reviews; they own no editable files or build slot.
Check Git status and HEAD before each edit/checkpoint; Claude commits on the
shared `main`. Stage only writing-owned files. Current dirty or untracked
`DiagramProof/` sources are Claude-owned; the current lane is first-drop coverage.

The full goal is unfinished: complete the independent diagram formalization
and assemble a new paper with the circular aggregate expansion and the
ordinary component expansion proved by these same diagram moves. The older
word/scan proof does not substitute for this route. Preserve historical
proof-note prefixes at `a3d076b`; append-only continuations remain authorized.

## Lean verification boundaries

- P0–P5 are verified under their contracts. The last Codex source checkpoint
  passed 649 axiom queries and source/import guards before the build transfer.
- `26b2d97`: the four right-attachment modules prove actual whole product
  components, HRV fibre merger, endpoint-omitted K/E gluing, paired integer
  recurrence transfer and measure decrease. No identity for the attached
  component is assumed. Codex read the successful focused log and all 719
  axiom outputs in exact query order; independent review approved the scope.
  Issue #8 is closed for this attachment subtask only, not all P9.
- `fb68ff5`: Claude reports no-articulation common-cover uniqueness and 724
  standard-axiom checks (`axioms-2.log`).
- `58b8b4b`: initial-path extension; Codex read successful `initpath-2.log`.
  Its new queries have not yet been added to the verification file, so the
  previous axiom audit does not cover it.
- `cdac9cc`, `cb723f6`, `f59bd96`: relational transport, alternating deletion
  and whole-component correction certificates. `altcert-2.log` passed.
  The earlier `compcorr-1.log` failed, but `iso-1.log` now records a successful
  rebuild of `ComponentCorrections` and its two direct dependencies. The new
  declarations still await the extended axiom audit.
- `3665a3d`: NN full-layer recurrence. Codex read successful `nn-5.log`
  (three deprecated-simp warnings). `e926c75` gives the DN full-layer
  recurrence; its final `dn-7.log` passes with unused-section-variable warnings.
  `e8bb9dd` adds component isolation and NN/DN certificates; `iso-1.log` passes.
  No new queries for these declarations were present. Prefix/first-drop
  coverage and final induction remain to be integrated and independently
  audited, together with the new certificate axioms and import closure.

Logs: `/lake-cache/ai-projects/requests/VerticalStripLLT/claude-right-attachment/logs/`.
Only Claude may perform the remaining focused builds and axiom checks.
Do not run `lake update` in response to the known manifest-path warning.

## Current writing checkpoint

The user-requested general diagram macros are in
[llt-diagrams.sty](docs/drafts/tex/llt-diagrams.sty), with a
[usage guide](docs/drafts/tex/README.md). Blank cells denote optional natural
edges; other cells specify selected, absent, forbidden, strict or cover
restrictions. Global conditions specify size, component and endpoint colors.
Area data can generate forbidden cells. Diagrams denote the resulting sums;
actual path figures fix every natural cell and denote individual states.
The two-page example guide and all macro-generated figures compile externally.
No external Overleaf source was edited.

The [ordinary draft](docs/drafts/ORDINARY_COMPONENT_DIAGRAM_PROOF.md) now
expands all previously listed local construction gaps: diamond, corrections,
preparation, restored crossing slides, two-chain paths, removable edges,
complete-diagram base, last-clique and initial-vertex inheritance, NN/DN
layers, attachment, prefix selection, four contact cases and final induction.
This is written mathematical proof, not a claim of completed formalization.
The whole-proof review has returned; its clarifications are incorporated.
Combined manuscript assembly and final paper/formalization comparison remain.

Pushed writing checkpoint `c734842` supplies the last-clique proof: connected
retained parts of selected blocks, sweep/lift/restoration, a fixed core spanning tree,
omitted leaves and exchanges through the shared edge. The temporary repair
when removing `ce` is explicit. Three read-only source reviews approved these
constructions, with geometry/count/endpoint clarifications incorporated.
The new `last-clique-tree.tex` figure uses the shared macros; its SVG was
rendered and visually inspected. Figure references and source maps are current.

The [circular draft](docs/drafts/CIRCULAR_E_EXPANSION.md) follows the checked
aggregate theorem. It separates terminal contact (factor `1+q`, doubled
area down six) from interior column reversal, and uses exactly Lean's
strict-edge length times proper-ancestor rank. DD-contact elimination is now
expanded with the two child row tables,
terminal eligibility, preservation of the remaining contacts, closing DN
move and cancellation. A new weighted restricted-sum figure shows the three
actual diagrams. Its auxiliary induction is explicitly on contact count,
since the resolved child has larger doubled area. Local boundary checks
still need expansion before combined assembly.

The whole ordinary-proof audit clarified the attachment hypothesis for every
target prefix, justified its preservation in the final induction, and expanded
the smaller-core overlap and corner-chain count arguments. Independent
review approved both DD row tables, the figure, child eligibility,
acyclicity and cancellation; residue-separation and notation clarifications
were incorporated. The opening/complete-diagram review found no K/E weight
or path/value confusion. We made the marked/unmarked complete case and its
two separate inductions explicit, and defined exact exterior agreement.

Writing previews/logs:
`/lake-cache/ai-projects/requests/VerticalStripLLT/diagram-formalization/tex-preview/`.
Latest checks: warning-free figure compilation, visual inspection, exact
rendered-source correspondence, SVG XML, local Markdown links and whitespace.
No Codex Lean build or mathematical computation ran during this increment.

## Next work and recovery

1. Assemble and edit the ordinary draft after the returned whole-proof audit;
   retain its correspondence to the actual checked diagram paths and keep
   compiler status outside the paper.
2. Expand circular local-boundary arguments, then assemble the
   combined manuscript with native vector figures and sparse TeX builds.
3. Incorporate Claude's final certificates/coverage/induction once verified;
   audit new theorem axioms, independent import closure and paper correspondence.

Primary sources: [assembled proof](docs/proofs/COMPONENT_DIAGRAM_COMPLETION.md),
[cleanup audit](docs/proofs/COMPONENT_DIAGRAM_AUDIT.md),
[formalization plan](docs/COMPONENT_DIAGRAM_FORMALIZATION_PLAN.md), and
[draft correspondence](docs/drafts/README.md). Use the
[combinatorics writing skill](/home/dev/.codex/skills/combinatorics-paper-writing/SKILL.md),
first-person plural prose and the authors' cell-diagram conventions.

The [archived handoff through `4a3f8cb`](docs/archive/diagram-writing-through-complete-base.md)
preserves chronology, exact earlier checks, ownership transfers and recovery
links. Lean MCP is rooted at RealRooted, so the designated owner uses focused
`lake-workspace` commands. Aristotle is available by CLI; no Codex remote
request, watcher or compiler is active. Docker supervisor discovery failed for
the persistent worker; read-only tmux inspection was possible. Do not bypass
supervisor input guards or stop/restart the worker.
