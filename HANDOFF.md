# VerticalStripLLT handoff

## Current status and ownership

The requested author revision is complete. The manuscript now explains the
LLT/chromatic comparison and Hwang's component refinement in its introduction,
collects all four recurrences in Proposition 2.7 and one TikZ boundary-path
figure, and uses numbered mathematical environments. It ends with the circular
LLT cumulant corollary, restores Per Alexandersson and Lilan Dai as authors,
and includes an AI-assistance statement. The cumulant deduction is a written
consequence of the component theorem, **not a new Lean formalization**.
The earlier coauthored draft was consulted read-only.

All bounded writing agents have released their files. Codex remains the
manuscript/figure owner; Claude's Lean ownership and build slot below are
unchanged. No Codex Lean build was started. The revised PDF and source bundle
are in the external `manuscript-revision/` directory described below; the
pre-author-edit tag and its original PDF remain intact.

The diagram formalization and the requested new manuscript draft are complete.
The paper has the user's two-part layout: circular LLT–HRV expansion through
diagram relations, then component expansions through those relations. The
second part proves the ordinary theorem and finishes with the finite
companion passage to **all circular components**. The aggregate theorem alone
is not used as a substitute for component refinement.

Ownership transfer at `b78312c` remains in force. Persistent Claude worker
`agent-verticalstri-motzki-c-001af720` owns all Lean sources, verification entry
points, [LEAN_COORDINATION](docs/LEAN_COORDINATION.md), and the **sole Lean
build slot**. Codex owns this handoff, project routing documentation, proof
maps and all manuscript sources/figures. Subagents `anchor_sizes`,
`semantic_extract` and `good_edges` have completed their assignments and
released all file ownership. No Codex compiler, remote request or watcher
remains active. Do not stop or restart the persistent worker.

Check Git status and HEAD before edits; Claude commits on shared `main`.
Stage only task-owned files. Do not run `lake update` for the known
manifest-path warning. Historical proof-note prefixes at `a3d076b` remain
preserved; append-only continuations were authorized.

## Verified mathematical scope

See [DIAGRAM_PROOF_COMPLETION](docs/DIAGRAM_PROOF_COMPLETION.md).

- `f2f396f` completed the ordinary diagram induction; `1b6d13e` exported and
  audited it. `55cfaf5` streamlined attachment and shared local lemmas.
- `77cabb9` derives the circular component theorem from this diagram proof
  through the finite circular companion. The compatible preimage is a union
  of complete ordinary components, possibly several, not an assumed single
  component. Independent review approved the public scope and this reduction.
- `98ad880` separates the older word proof into `WordProof/` and removes dead
  diagram modules. The circular theorem's 360-file closure is unchanged and
  contains no word/scan theorem. The ordinary and circular public contracts
  have no recurrence certificate, balance or assumed semantic-bridge premise.
- `1a9eb1f` gives the diagram theorems the plain names
  (`component_strict_eq_elementary`, `..._of_forward` and relatives); the word
  proof's theorems end in `_by_words`, and the interim `_by_diagrams` names are
  deprecated aliases. The 215 diagram modules sit in 13 proof-step folders
  under `DiagramProof/`, described in `Components/DiagramProof.lean`.
  Docstrings and linter fixes changed no statement.
- Latest full library build passes: **2367 jobs**, `full-build-1a9eb1f.log`;
  the only warnings are seven unused hypotheses in public `WordProof`
  statements. All **815** dedicated axiom queries and the 2814
  `Verification.lean` queries use only standard Lean axioms or none. The
  preceding 860-query audit at `77cabb9` also passed; the difference is unused
  helpers.

Logs live under
`/lake-cache/ai-projects/requests/VerticalStripLLT/claude-right-attachment/logs/`.
Immutable copies `axioms-77cabb9.log`, `axioms-98ad880.log`,
`axioms-1a9eb1f.log` and `verification-1a9eb1f.log` have hashes in the
completion report. The working log `axioms-4.log` was reused; do not infer
its contents from an older count. A
[workflow suggestion](suggestions/commit-stamped-axiom-logs.md) records this.

The circular aggregate theorem has its separate
[CIRCULAR_COMPLETION](docs/CIRCULAR_COMPLETION.md) audit. Both aggregate and
component results concern the actual coloring and integer-cover HRV semantics.

## Manuscript and diagram macros

Canonical prose and source correspondence:
[docs/drafts/README.md](docs/drafts/README.md). The introduction is followed by
`CIRCULAR_E_EXPANSION.md`, `ORDINARY_COMPONENT_DIAGRAM_PROOF.md` and the final
Part 2 subsections in `CIRCULAR_COMPONENTS.md`. The latter include explicit
HRV deletion cancellation, the full finite coefficient argument, actual
cover-preserving flips and the compatible-lift union of ordinary components.
We do not claim each circular bounce/reversal restricts to a single component.

The revised manuscript is **41 pages with 13 vector figures**. The original
tagged baseline was 35 pages. The general
[llt-diagrams.sty](docs/drafts/tex/llt-diagrams.sty) and its
[usage guide](docs/drafts/tex/README.md) implement diagrams as restricted sums:
optional/selected/absent/forbidden/strict edge restrictions, cover conditions,
fixed-size layers, component restrictions and endpoint colors. The four-recurrence
figure uses actual north/east/diagonal boundary paths; other restricted sums
use the shared sparse TikZ renderer. Individual path states
are the fully specified special case. Native TeX sources generate all SVGs.
No external Overleaf manuscript was edited.

Rebuild with `python3 docs/drafts/build_manuscript.py --output /external/path`.
Python performs document conversion only. The assembler creates a PDF,
self-contained TeX source bundle and SHA256 input manifest. Build products
remain external:

`/lake-cache/ai-projects/requests/VerticalStripLLT/diagram-formalization/manuscript-revision/`

Files: `manuscript.pdf`, `manuscript.tex`, `manuscript-source.zip`,
`source-manifest.json`. Figure inspection images are in `figure-review/`;
PDF page previews are alongside the manuscript. The author metadata matches
the earlier Alexandersson--Dai draft.

Verification: 41-page PDF and two-page macro guide compile without warnings
or box overflows. The 152 labels are unique, all 111 equation/theorem/figure
references resolve, and all 24 bundled source inputs match their manifest.
There are 5 theorem, 27 lemma, 9 proposition, 12 definition, 2 corollary,
1 example and 43 proof environments. The introduction, grouped-recurrence
pages and final corollary/AI statement were visually inspected, as were all
13 vector figures. Independent reviews checked the new comparison, recurrence
scope and cumulant deduction. Root corrected the concrete ND target and drew
actual north/east/diagonal steps in the recurrence figure. All SVG previews
were regenerated from the current native sources.

The revision PDF SHA256 is
`caeba63c595cfa02dd012b365ce8b9297b8c06a415a43a53229909ccbedd7529`.
Paper-cache entries 496 (AS22), 497 (Hwang) and 498 (Dołęga--Kowalski)
contain exact-version PDFs, source archives and extracted text; precise
locators are in the draft README. The paper-cache database discovery call
`query_arxiv_sf` was unavailable because `pymysql` is missing; a web metadata
lookup located Hwang's arXiv ID, after which all source reading used the cache.


## Baseline for author revisions

Annotated GitHub tag `draft-v1-before-author-edits` points to `80c106d`, the
verified two-part draft produced with the combinatorics paper-writing skill.
Preserve this tag for comparison with the user's revisions and later skill
improvements. Compare tracked prose and figures with
`git diff draft-v1-before-author-edits -- docs/drafts/`.
If revisions are made to exported TeX, rebuild the tagged canonical sources
to recover the baseline TeX before comparing. The tag precedes the subsequent Lean refactoring and this author-requested
revision. The baseline 35-page PDF was submitted to R211 under receipt
`20261001T094755-e431ded0d3cb`; this revision has not been printed.

## Follow-up

The requested formalization and new draft are delivered. Further author
editing, selecting publication formatting, or editing the external Overleaf
copy would be subsequent tasks. Continue using the
[combinatorics paper-writing skill](/home/dev/.codex/skills/combinatorics-paper-writing/SKILL.md)
and preserve the two-part architecture and diagram proof correspondence.

The [handoff archive through `0c87ed0`](docs/archive/diagram-writing-through-native-figures.md)
preserves earlier proof work, ownership transfers and verification history.
Its unfinished-formalization statements are superseded here. Lean MCP is
rooted at RealRooted; the designated owner uses focused `lake-workspace`
commands. Aristotle remains available through the CLI when useful.
