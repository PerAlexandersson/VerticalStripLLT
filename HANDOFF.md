# VerticalStripLLT handoff

## Active ownership — Claude owns Lean; Codex owns the writeup

Transfer pushed at `b78312c`, 2026-10-01. Persistent Claude worker
`agent-verticalstri-motzki-c-001af720` owns all Lean sources, the verification
entry points, [LEAN_COORDINATION](docs/LEAN_COORDINATION.md), and the **sole
Lean build slot**. Codex and its subagents must not edit Lean or run builds.
Current dirty Lean files, including `CircularConsequences.lean`, belong to
Claude's further refactoring/development; they are not part of the completed
ordinary checkpoint below.

Codex owns this handoff, mathematical prose, formalization maps and plan,
`docs/drafts/`, figures and manuscript assembly. Read-only subagents
`semantic_extract`, `anchor_sizes` and `good_edges` are reviewing the final
circular proof, introduction/scope and ordinary proof correspondence. They
own no editable files or build slot. Check status and HEAD before edits;
Claude commits on shared `main`. Stage only task-owned writing files.

The diagram formalization is complete. The full goal remains active until
we assemble and review the combined paper: circular aggregate expansion and
ordinary component expansion by the same diagram moves. Preserve historical
proof-note prefixes at `a3d076b`; append-only continuations remain authorized.

## Verified ordinary diagram theorem

See [the completion audit](docs/DIAGRAM_PROOF_COMPLETION.md) for exact theorem
scope, proof dependencies and verification. The proof was completed at
`f2f396f`, exported and audited at `1b6d13e`, then streamlined at `55cfaf5`.
Independent source review approved the full theorem and induction, and a
second review confirmed the refactor preserves all theorem contracts and
diagram semantics. The public strict, weighted and positivity theorems have
no recurrence-certificate or assumed semantic-bridge hypothesis.

- Full library build passed at `1b6d13e` (2364 jobs, `full-build-2.log`).
- Focused post-refactor build passed through `Consequences` (1921 jobs,
  `clean-4.log`).
- `axioms-3.log` and the fresh `axioms-4.log` each match all **856** committed
  queries in order after namespace qualification; all use only standard
  Lean axioms or none. The earlier literal-name mismatch was a comparison
  error, corrected by the independent reviewer; no provenance gap remains.
- Static review at `1b6d13e`: 289 project files in the final theorem closure;
  314 in the dedicated verification closure including its root (313 imported
  files). No earlier word/scan component proof is an input. All 237 diagram
  modules passed source guards and line-width checks.

Logs: `/lake-cache/ai-projects/requests/VerticalStripLLT/claude-right-attachment/logs/`.
No Codex build is needed. Do not run `lake update` for the known manifest-path
warning. The separately checked circular aggregate theorem remains as recorded
in [CIRCULAR_COMPLETION](docs/CIRCULAR_COMPLETION.md).

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
The independent ordinary diagram formalization is now verified as recorded above.
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
since the resolved child has larger doubled area. The remaining local
arguments are now expanded: explicit NN/DN coloring involutions, cyclic HRV
diamond cases, seven separated-ND identities, and the reversal area and
exterior-boundary checks. Read-only reviews checked the coloring, separated
ND and reversal arguments; their precise hypotheses were incorporated.

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

The latest writing increment adds `INTRODUCTION.md` and `references.bib`;
the ordinary source metadata was checked against arXiv:2004.09198. A new
weighted direct-relation figure uses the shared sum macros. The three older
SVG-only figures (initial crossing, reversal and attachment) now have native
TeX sources, compiled externally and visually checked. All manuscript SVGs
are generated from editable TeX. The next production task is the combined
PDF/TeX assembly, using the Markdown sections as the canonical prose.

## Next work and recovery

1. Assemble the introduction and two proof sections into one manuscript using
   the canonical Markdown prose and all native TeX figure sources.
2. Inspect the complete PDF, references and notation; incorporate the final
   paper/formalization correspondence reviews. Compiler status stays outside
   the manuscript.
3. Checkpoint and push the reproducible draft and its build instructions.

Primary sources: [assembled proof](docs/proofs/COMPONENT_DIAGRAM_COMPLETION.md),
[cleanup audit](docs/proofs/COMPONENT_DIAGRAM_AUDIT.md),
[formalization plan](docs/COMPONENT_DIAGRAM_FORMALIZATION_PLAN.md), and
[draft correspondence](docs/drafts/README.md). Use the
[combinatorics writing skill](/home/dev/.codex/skills/combinatorics-paper-writing/SKILL.md),
first-person plural prose and the authors' cell-diagram conventions.

The [archived handoff through `0c87ed0`](docs/archive/diagram-writing-through-native-figures.md)
preserves earlier status and checks; its unfinished-formalization statements
are superseded above. Lean MCP is rooted at RealRooted, so the designated
owner uses focused `lake-workspace` commands. Aristotle is available by CLI;
no Codex remote request, watcher or compiler is active. Docker supervisor
discovery failed for the persistent worker; read-only tmux inspection was
possible. Do not bypass supervisor input guards or stop/restart the worker.
