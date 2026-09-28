# Manuscript synchronization

## Shared cell diagrams — 2026-09-28

The author requested the diagram conventions of the paper with Robin for
both the circular HRV proof and the ordinary component argument. Examples
4.1 and 5.3 of the published Alexandersson--Sulzgruber paper were inspected.
`proof-diagrams.tex` now provides `LLTCells` and `LLTSelectionTriangle`:
yellow diagonal labels, gray cells without ascent weights, and configurable
math entries. The circular NN/DN figure, circular four-selection identity,
and ordinary diamond now use the same macros. Their captions/text distinguish
weighted diagram sums from unweighted selected relations. Circular labels
denote integer lifts with periodic exterior data retained.

The preview is now 13 pages. It compiles without warnings or overfull/underfull
boxes; pages 4 and 9 were visually inspected. The former source files and PDF
are preserved under the external `local-diagram-style/before/` receipt, and
the new sources, preview and logs under `local-diagram-style/build/` in the
project requests cache. The proof text and theorem statements are unchanged
apart from explaining the new notation. The new conditional five-vertex DN
comparison proof remains in research notes, not in the manuscript.

## Separate circular-first draft — 2026-09-28

The user found the previous overhaul difficult to follow and requested a new
file closer to the original. The new Overleaf entry point is `dyck-first.tex`,
with `dyck-first.pdf` (12 pages) and source sections in `dyck-first/`. It proves
the aggregate circular formula first, by unicellular/bounce relations and
half-square-area/strict-rank induction; contact overlap uses interval reversal.
Ordinary flip components follow, with the word calculation moved to an appendix.
Diagrams explain the objects and reductions where they are needed. Existing main/sections and
the archived original drafts are preserved. `DYCK-FIRST-MAP.md` records exact
correspondence, including the separate formal source for the root-alias endpoint.

Independent Astra review of the circular proof supplied incorporated corrections
to periodic HRV transport and overlap geometry. Luna reviewed the historical
ordinary route: the completed proof is the word/Cauchy/sink argument, not the
old unfinished component recurrence program. The weak/h consequence is written
separately via stabilization and the QSym involution. Source references are
resolved and the external LaTeX build has no warnings. Figures were visually
inspected. Build artifacts remain in the `manuscript-dyck-first/` request cache.
No Lean code or build changed. See the current handoff for final review status.

The subsequent user clarification restored the ordinary diamond lemma as
Section 4.2, with its coloring/HRV proof and an inline four-state diagram.
The existing four-vertex example explains why fixed-diagram diamonds alone
cannot reduce the component to chain states. The word argument remains the
completed global step. The updated PDF is 12 pages and builds cleanly; the new
page and diagram were visually inspected. No additional formalization is claimed.

## Previous overhaul — 2026-09-27

The user-authorized proof overhaul is complete in the existing Overleaf project:

`/home/paxinum/Dropbox/Apps/Overleaf/LLT flip/`

The previous entry point is `main.tex`; `main.pdf` is the reviewed 20-page preview.
The original main and v9 drafts, bibliography, editorial audit and old PDF were
preserved before editing in `archive/2026-09-27-before-finite-proof/`, with a
verified SHA-256 manifest. The root v9 source and bibliography are unchanged.

The two replacement proof sections follow the finite strict/e route checked at
`0b64954` (verification record `d28981e`). The ordinary section uses ordered color
products, conjugation and signed-sink extraction. The circular section uses
simultaneous deletion identities, contracted gains, coefficient-preserving flips
and a flip-closed ordinary preimage. Internal `PROOF-MAP.md` in the Overleaf project
records theorem labels and the corresponding Lean declarations.

The author requested the style and terminology of the Alexandersson–Sulzgruber
paper, removal of TODOs/AI notes, and implementation references only in internal
TeX comments plus a brief closing formalization note. The active draft follows
these preferences. Its weak/h consequence uses the separately written
stabilization and involution argument. The retained cumulant and chromatic
material is not described as formalized.

Six new/reworked proof figures use reusable TikZ primitives in
`proof-diagrams.tex`; the existing cell and local-relation illustrations remain.
Astra reviewed the circular proof and Luna reviewed the ordinary argument,
read-only and without builds. Applicable clarifications were incorporated.
No mathematical defect was found in those reviews.

The isolated final LaTeX build has no unresolved citations/references, LaTeX
warnings or box warnings. The opening, all six proof figures and the closing
note were visually checked. Sources and preview match byte-for-byte before
copying the final PDF back to Overleaf. All archive hashes were rechecked.
Build logs and intermediate artifacts remain under
`/lake-cache/ai-projects/requests/VerticalStripLLT/manuscript-overhaul/`.
Only current sources are staged there, avoiding the old root aux/bbl files.

The Overleaf folder is not a Git repository. Its manuscript sources remain there;
this repository records the correspondence and workflow status. No Lean source
was modified or rebuilt, and no account, worktree or supervisor worker changed.
All auxiliary assignments are complete and released.
