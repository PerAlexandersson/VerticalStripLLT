# VerticalStripLLT handoff

## Current status and ownership

On 2026-10-15, the Chromatic P-array RSK worker reclaimed only
`docs/chromatic-p-array-rsk/`, `experiments/chromatic-p-array-rsk/`, and its
focused `HANDOFF.md` entry to study the total simple-reflection action
transported from the SSYT crystal.  The immediate tasks are to implement the
Lusztig/Kashiwara string reflections on colorings, verify involution,
weight-swap, commutation, and braid relations through rank five, and compare
them exactly with the Shareshian--Wachs odd-component color switches.  All
previous exclusions and the absence of a Lean build slot remain in force.

On 2026-10-15, at the user's request, the Chromatic P-array RSK worker
reclaimed only `docs/chromatic-p-array-rsk/`,
`experiments/chromatic-p-array-rsk/`, and its focused `HANDOFF.md` entry to
expose the conjugated Kashiwara operators as explicit coloring-level
functions and verify their normal type-A structure.  The insertion tableau
must remain fixed, ascent must remain constant, and the finite checks must
cover string parameters and highest-weight/component behavior, not merely
partial inverse identities.  The marked-coloring/HRV, circular LLT, Lean,
and manuscript lanes remain excluded, and this worker still holds no Lean
build slot.  This task is now complete and those paths are released.

The checkpoint `4b906e3` adds explicit coloring-level `e_i` and `f_i`, a
complete fixed-alphabet crystal-graph constructor and DOT exporter, string and
highest-weight checks, and an inverse-Kostka/Kashiwara defect census.  For all
64 natural unit interval orders through rank five, the complete `k=n` graphs
have 56,993 vertices, 99,360 directed edges, and 2,065 components in total;
every component is a fixed-`T` copy of `B_k(lambda)`.  At rank five alone the
counts are 55,125 vertices, 96,968 edges, and 1,849 components.  The highest
coloring in the component indexed by `T` is exactly
`R_lambda^{-1}(T)`.  The one-empty-color census checks 292,322 rank-five
string identities and 120,659 lowering edges.

Astra independently assessed the locality data.  This particular transported
crystal is global even for a chain: in one-based colors
`f_1(112)=221`, `f_1(132)=322`, and the colorings `1134`, `1143` have the same
weight, ascent, and labeled `1/2` restriction but map to `2134`, `4321`.
Thus fixed reading-word signatures, Ehrhard-style two-row moves, active-pair
component switches, and naive standardization are all excluded for this map.
The Shareshian--Wachs involution commutes with the recording-tableau operator;
the first obstruction is the rank-two failure to commute with the reverse
inverse-Kostka involution.  Through rank five, 309 of 1,120 tested
inverse-Kostka/operator pairs are defects (226 definedness, 83 unequal value).
The next focused experiment is a marked-trace classification of those defects
by Allen--Celano--Mason `psi/theta` event words.  Tests, Clippy with warnings
denied, the 12.9-second full release census, DOT smoke output, and
`git diff --check` all passed.

On 2026-10-15, the Chromatic P-array RSK bijection worker completed a separate
research lane for an explicit weight- and ascent/inversion-preserving map from
proper colorings/P-arrays of natural unit interval orders to pairs of a
P-tableau and an ordinary semistandard tableau.  During the task it owned only
`docs/chromatic-p-array-rsk/`, `experiments/chromatic-p-array-rsk/`, and its
focused updates to `HANDOFF.md`, on branch `chromatic-p-array-rsk` in an
isolated worktree; those paths are now released.  The first milestone was
mathematical: identify the exact
Shareshian--Wachs/Gasharov and LGV signed sets, involutions, and any
Garsia--Milne alternating-path certificate before writing executable code.
Only after that audit may the worker add the bounded Rust prototype and test
natural unit interval orders beginning with `n <= 5`.  It does not own or
touch the marked-coloring/HRV e-positivity project, Lean sources, circular LLT
work, or manuscript files, and it holds no Lean build slot.

The mathematical audit has fixed the common signed set in
`docs/chromatic-p-array-rsk/SIGNED_SETS.md`.  The source-side `asc` statistic is
first converted to the Shareshian--Wachs array `des` statistic by color
complement followed by their odd-component Bender--Knuth switches; a second
such normalization sends an arbitrary packed content `mu` to the partition
`mu^+`.  On the common signed set, the first involution must realize the
historically harder reverse inverse-Kostka identity, while the second is the
Shareshian--Wachs array involution conjugated by those normalizations.  Thus a
bare LGV tail switch is not enough: it proves Jacobi--Trudi locally, but does
not itself supply the required `K^{-1}K` cancellation.  The implemented
replacement is Allen--Celano--Mason Algorithm 5.4, translated by
`sigma=pi^{-1}` and conjugated by ordinary tableau Bender--Knuth maps.  The
note also records explicitly that Ehrhard's operators
are only weight-shifting partial inverses, not normal type-A Kashiwara
crystals.  Astra's completed read-only audit confirmed the inverse-Kostka
orientation and conjugated-involution closure, supplied the exact import of
Allen--Celano--Mason Algorithm 5.4, and showed that Kim--Pylyavskyy extends to
repeated colors by block standardization on its avoidance class.

The bounded Rust prototype and its durable report are now in
`experiments/chromatic-p-array-rsk/` and
`docs/chromatic-p-array-rsk/COMPUTATION.md`.  It exhaustively verifies all 64
natural unit interval orders through `n=5`, all 13,701 packed proper
colorings, every weight/q fiber, both involutions, all forward and reverse
alternating paths, and exact target coverage.  It separately verifies all 376
reverse inverse-Kostka endpoints through rank five.  The longest fully local
trace has 120 events.  The Kim--Pylyavskyy avoidance test identifies 63
eligible orders and
13,437 eligible colorings; the sole excluded rank-five order has Hessenberg
code `(2,4,4,5,5)`, namely `P_(3,1,1),5`.  The smallest fixed-shape LGV and
same-cut obstruction is the exact `n=2`, `mu=(1,1)`, `nu=(2)` fiber; a naive
all-tail exchange first changes q at `n=4` for `m=(1,3,3,4)` and
`G={{2,3}}`.  The map also handles weak contents in a fixed alphabet: 67,682
rank-five cases with one inserted empty color class were checked.  Transported
ordinary Kashiwara operators on `Q` were verified to be partial inverses that
preserve properness and `asc`, with the expected simple-root weight changes.
No Lean source, Lean build, marked-coloring/HRV file, circular LLT file, or
manuscript file was touched.

The signed-set checkpoint is `1ec0ea3`; the verified Rust/report checkpoint
is `f77cd34`.  The branch is `chromatic-p-array-rsk`, pushed to `origin`.
On 2026-10-15 the user asked this worker to resume ownership of the same three
paths until the finite lexicographic matching had been replaced by a full
constructive bijection.  That milestone is complete: the local
Allen--Celano--Mason trace is integrated into every forward and inverse
Garsia--Milne path, and no global fiber matching remains.  The same exclusions
and absence of a Lean build slot remained in force.  The verified constructive
checkpoint is `e9b44d4`; the worker has released its three owned paths again.

On 2026-10-13, the Lilan revision integration worker completed the
author-requested Overleaf upload and email notification.  The current main TeX
file, bibliography, seven section files, and verified PDF were synchronized to
`/home/paxinum/Dropbox/Apps/Overleaf/LLT flip/paper/`; byte comparisons confirm
that they match GitHub.  Older Overleaf drafts, archives, project notes, and
already-identical manuscript files were untouched.  A fresh external build
from the synchronized snapshot in
`/tmp/verticalstripllt-overleaf-verify-Z4Vveb` produced the same 28-page PDF,
with no TeX, bibliography, reference, citation, or box warnings, and passed
`qpdf --check`.  An email summarizing the revision and linking GitHub was
successfully delivered to the Nankai address Lilan used for UID 88, with the
current PDF attached.  The worker has released `HANDOFF.md` and all external
manuscript files.

On 2026-10-13, the Lilan revision integration worker completed the
author-approved wider page geometry from Lilan's revision.  The main file now
uses letter paper with 2 cm top/bottom and 3 cm left/right margins (and a 2 cm
margin-note width), reducing the manuscript from 37 to 28 pages without any
prose or mathematical change.  The manuscript was built only in
`/tmp/verticalstripllt-wide-pages-Dly3PP`; the final build has no BibTeX,
LaTeX, reference, or box warnings and passes `qpdf --check`.  All pages were
inspected at thumbnail scale, with the title, dense figure/proof pages,
Section 7.3, and bibliography additionally inspected at full size.  The
rebuilt `paper/llt-flip-classes.pdf` has SHA256
`6e3104e75767ad1b927ab1819d5570a470b18d416eb554ac45b174517c9188ea`.
The Overleaf tree remained read-only, and no Lean source or Lake command was
used.  The worker has released `HANDOFF.md`, `paper/llt-flip-classes.tex`, and
`paper/llt-flip-classes.pdf`.  The verified layout checkpoint is `b3fe6b5`.

On 2026-10-13, the Lilan revision integration worker completed the
author-approved comparison of Hwang's and the LLT flips, Section 5 readability
pass, and Section 7.3 literature clarification.  The preliminaries now state
Hwang's local move precisely: it reverses a source or sink fork in an acyclic
orientation, whose outer vertices are nonadjacent.  The LLT move instead acts
inside a triangle, retains its long edge, and uses covers in the
ascending-and-strict-edge posets.  Section 7.3 explains that OpenAI's aggregate
chromatic theorem does not settle Hwang's classwise conjecture, while this
paper proves the LLT classwise analogue, and it asks for a relation between the
two genuinely different component decompositions.

The registered `arxiv-symmetricfunctions` index, Hwang's exact v2 manuscript,
and the current OpenAI manuscript were checked.  Searches for later work on
Hwang's local flips and for a bijection matching this paper's highest-reachable
component theorem found no general resolution; known special cases of Hwang's
conjecture do not settle the question stated here.  Section 5 received only
short strategy paragraphs before its complete-graph, deletion, last-clique,
and first-vertex arguments; no proof step or notation changed.

The manuscript was built only in
`/tmp/verticalstripllt-section57-9peFpB`.  The final 37-page build has no
BibTeX, LaTeX, reference, or box warnings, passes `qpdf --check`, and the
changed pages were inspected.  The rebuilt `paper/llt-flip-classes.pdf` has
SHA256
`875b2d6c1bfa4d2d5967338e06cd0142395dbf640df9ced6376524f654391f18`.
The verified flip-comparison and readability checkpoint is commit `5131de0`.
No Lean source or Overleaf file was touched.  The worker has released
`HANDOFF.md`, `paper/sections/preliminaries.tex`,
`paper/sections/connectivity.tex`, `paper/sections/consequences.tex`, and
`paper/llt-flip-classes.pdf`.

On 2026-10-13, the Lilan revision integration worker completed the
user-requested arXiv-index cross-check and literature update in
`paper/sections/introduction.tex` and `paper/references.bib`.  The registered
`arxiv-symmetricfunctions` API was current through 2026-10-13 and confirmed
the metadata and publication status of all eleven arXiv records checked.  This
supplied missing arXiv identifiers for AS22, the Ellzey FPSAC paper and Hikita,
and Hwang's published DOI.  The introduction now distinguishes Hikita's
numerical nonnegativity for each fixed positive real `q` (with `q=0` by
specialization) from OpenAI's later coefficientwise theorem in `N[q]`, citing
the exact Corollary 1.2 and Theorem 1.1.

The `paper-cache` full-text archive endpoint was unavailable because its
archive database is not mounted in this container; the exact cached Hikita v2
source and OpenAI's official September 24 manuscript were checked instead.
An external `latexmk` build has zero BibTeX, LaTeX, reference, or box warnings;
the 37-page PDF passes `qpdf --check`, and the revised introduction and final
bibliography page were inspected.  The rebuilt `paper/llt-flip-classes.pdf`
has SHA256
`9b7636a5eb49decfc36f63f27d0b579f1e3e1670bcd76a99d37db660193a85a6`.
The verified literature checkpoint is commit `16771e0`.
No Lean source or Overleaf file was touched.  The worker has released
`HANDOFF.md`, `paper/sections/introduction.tex`, `paper/references.bib`, and
`paper/llt-flip-classes.pdf`.

On 2026-10-13, the Lilan revision integration worker completed the requested
bibliography-metadata cleanup in `paper/references.bib`.  The Abreu--Nigro and
Lee preprints now use their published journal records; the Ellzey FPSAC paper
uses its official SLC citation; genuine arXiv/preprint items use suitable entry
types; and the Hikita paper is recorded as electronically published, without
inventing volume or page data.  An external `latexmk` build has zero BibTeX,
LaTeX, reference, or box warnings; the 36-page PDF passes `qpdf --check`, and
the bibliography pages were inspected.  The rebuilt
`paper/llt-flip-classes.pdf` has SHA256
`1366c6e313fa65c8e5e0f7b21cb78a184e9b3e24fae137e903d91d62dad85310`.
No Lean source or Overleaf file was touched.  The worker has released
`HANDOFF.md`, `paper/references.bib`, and `paper/llt-flip-classes.pdf`.  The
verified bibliography checkpoint is `53af2c9`.

On 2026-10-13, the Lilan revision integration worker adopted the manuscript
revision after the former Claude owner session was confirmed absent by
`supervisor-tool report`.  During this bounded task, the worker owned `HANDOFF.md`,
`paper/llt-flip-classes.tex`, `paper/llt-flip-classes.pdf`,
`paper/references.bib`, and the seven files under `paper/sections/` for the
task of reconciling Lilan Dai's UID 88 comments with the current GitHub
manuscript.  The attachments were inspected only in an external `/tmp`
directory, and the Overleaf tree remained read-only.  No Lean source, Lean
build slot, deployment, print job, or external correspondence was in scope.

The UID 88 reconciliation is complete.  Comments 1--11 and 13--36 were
applied or adapted to the current notation and architecture.  Comment 12 was
already satisfied by the newer GitHub contact figure and caption.  Comment 37
was not applied: its `geometry` override is presentation-only and predates the
newer GitHub figures.  The postscript about unspecified recent work was
deferred because it identifies no paper or citable claim.  In particular, the
revision keeps the later GitHub figures and notation rather than copying the
older magenta Overleaf source wholesale.  Section 5 now states the
occupied/vacant exchanges, the four restoring flips, the edge-count bounds and
the exceptional-cardinality argument explicitly.

The manuscript was built only in
`/tmp/verticalstripllt-lilan-uid88-FK61nC/build`.  The 36-page PDF has SHA256
`253f3e6892f8f79c8ece148a5bad48638e5e8e88b7ebc372491c6541d65a0fff`.
The final LaTeX log has no LaTeX, reference, overfull or underfull warnings;
`qpdf --check` passes, `git diff --check` passes, and the revised pages were
visually inspected.  BibTeX retains eight incomplete-metadata warnings,
including the page-free electronic Hikita journal record.  No Overleaf file
was modified and no Lean build was run.
The verified manuscript checkpoint is `8010a2b`; the integration worker has
released all adopted files.

The active author-directed manuscript remains the **component-first** `paper/`,
per `paper/PLAN.md` and `docs/LEAN_COORDINATION.md`.  The former Claude
ownership is superseded by the adoption above; the older `docs/drafts/`
sources and the aggregate-first descriptions below are retained history, not
the current manuscript architecture.

Codex reviewed `paper/` at `3a28bc1`, including the figures/examples at
`8af0161`, without editing it. See
[the review](docs/proofs/CLAUDE_MANUSCRIPT_REVIEW_2026-10-01.md) for exact fixes:
admissible versus acyclic orientations in Theorem B; a missing cover hypothesis
in one connectivity paragraph; an overbroad Lean-verification claim; and
smaller wording/presentation follow-ups. The two independent read-only reviews
found no substantive gap in the ordinary or circular component arguments.
The isolated 33-page TeX build passes without warnings or box errors; all 79
labels and 156 references check. Codex owns only this review and handoff update.
The review agents have finished and hold no files. No Lean build was run.

## Earlier Codex manuscript checkpoints

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
At that earlier checkpoint, Claude worker
`agent-verticalstri-motzki-c-001af720` owned all Lean sources, verification
entry points, `docs/LEAN_COORDINATION.md`, and the sole Lean build slot
(transfer at `b78312c`).  The session no longer exists; this manuscript-only
task did not adopt any of those Lean files or invoke the build slot.

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
