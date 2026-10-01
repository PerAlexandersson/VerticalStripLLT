# VerticalStripLLT handoff

## Current status and ownership

The AS22 case audit after `8eb8550` found an exposition omission in the
aggregate direct NN/DN orientation proof. The four-selection HRV identity
replaces the finer AS22 orientation tables, but its assembly was too terse.
The manuscript now gives separate source/target edge tables, the NN target's
two states, both DN triangles, exterior-selection reindexing for the empty
local selection, and transitive-closure matching for the full local selection.
Independent read-only review checked this against
`Circular/FirstBounceOrientation.lean`, `FirstBounceOrientationMatching.lean`,
`DNOrientationBlocks.lean` and `SecondBounceOrientation.lean`.
No Lean source or build was touched. The rebuilt PDF is 46 pages, with no
warnings or box overflows; source hashes and all references were checked.
Codex owns these manuscript/handoff edits; `bounce_case_audit` has finished
its read-only review and holds no files.

After `9702fef`, the introduction explicitly distinguishes the AS22 diagram
method and cited background from proof dependencies: we prove the required
circular local identities and recover the ordinary expansion without assuming
the AS22 expansion or uniqueness theorem. The component identity further
refines both cases. Also repaired two malformed internal manuscript links caused
by the preceding notation pass. The rebuilt manuscript has 45 pages and no
LaTeX warnings or box overflows. Ownership and mathematical scope are unchanged.

The author's diagram and exposition revision after `e4c7159` is complete.
The six-section outline is recorded in
[REVISION_OUTLINE](docs/drafts/REVISION_OUTLINE.md): introduction and both main
theorems; circular aggregate expansion; ordinary component recurrence;
connectivity by flips; circular components; cumulants. The long connectivity
proof remains in the main text, now in `ORDINARY_FLIP_CONNECTIVITY.md`, after
its precise statement and role in the ordinary recurrence. Its already-proved
initial-path extension is explicit in the statement.

The manuscript states the original Alexandersson--Sulzgruber four relations,
then their shifted forms and exact induction orders. The source uniqueness
proof uses the height of the FIRST east step. The ordinary component proof
uses vertex count, total natural area and area moment; the circular aggregate
proof has its separate two-statistic order. Auxiliary DD derivations are
explicitly distinguished from outer induction calls.

Gray denotes the exterior of the path. Generic diagrams use zigzags for
arbitrary intervening portions and adjacent steps for consecutive vertices.
The author-supplied Robin-source snapshot and earlier Alexandersson--Dai TikZ
pictures were consulted read-only. A new three-vertex flip figure explains
a full component and its elementary contribution in the introduction.
Path steps use typewriter letters, evaluations use sans-serif K/E, and
unnecessary indexed states and proof-stage names have been removed.

Codex owns this handoff, manuscript/figures and proof maps. Bounded agents
`diagram_spacing_audit` and `notation_audit` have released their files.
Persistent Claude worker `agent-verticalstri-motzki-c-001af720` still owns all
Lean sources, verification entry points, `docs/LEAN_COORDINATION.md`, and the
sole Lean build slot (transfer at `b78312c`). No Codex Lean build or remote
proof job was started. Do not stop or restart that worker.

Check Git status and HEAD before edits; Claude commits on shared `main`.
Stage only owned files. Preserve the pre-author-edit tag and its original PDF.
No external Overleaf file was edited and the revised PDF has not been printed.
The author/AI statement correction at `e4c7159` remains: no cumulant
formalization caveat in the manuscript; the published attribution remains.
Internal scope is unchanged: no new Lean theorem is claimed for that corollary.

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
`CIRCULAR_E_EXPANSION.md`, `ORDINARY_COMPONENT_DIAGRAM_PROOF.md`,
`ORDINARY_FLIP_CONNECTIVITY.md`, `CIRCULAR_COMPONENTS.md` and `CUMULANTS.md`. The latter include explicit
HRV deletion cancellation, the full finite coefficient argument, actual
cover-preserving flips and the compatible-lift union of ordinary components.
We do not claim each circular bounce/reversal restricts to a single component.

The revised manuscript is **46 pages with 14 vector figures**. The original
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

Verification: the 46-page manuscript and four-page macro guide compile
without warnings or box overflows. The 171 labels are unique, all 130
references resolve, and all 26 source inputs match the bundle manifest.
There are 5 theorems, 27 lemmas, 10 propositions, 13 definitions, 2 corollaries,
2 examples and 43 proofs. The new introduction, original and shifted
recurrences, induction table and ordinary proof strategy were visually
inspected, as were all 14 figures. All SVG previews were regenerated.
Independent reviews checked the original-source correspondence, induction
orders, moved connectivity dependency, diagram spacing and notation changes.
`git diff --check` passes. The complete Lean proof is unchanged.

The revision PDF SHA256 is
`dd15b8d858532c459908e21013fac95cffb577f823b14f202bd1e0b4fdce2683`.
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
