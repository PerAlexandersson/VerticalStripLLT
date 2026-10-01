# Review of the component-first manuscript

Reviewed `paper/` at `3a28bc151e12144e410478bb8eb8bd10a58835ae`, including
Claude's figure/example revision `8af0161`. The subsequent introduction
commit only adds the formalization URL. This is a read-only review of the
manuscript: Claude retains ownership of `paper/` and all Lean sources.
Codex owns this review and the handoff update. No Lean build was run.

The component-first organization is the author's recorded decision in
`paper/PLAN.md`; it supersedes the earlier aggregate-first draft. The
introduction now states the principal results and explains the mechanism.
The marked attachment argument, separate NN/DN layer calculations, and the
union of ordinary classes in the circular reduction are retained. Two
independent read-only reviews found no substantive gap in those arguments.
This is a source review, not a new formal certification of the prose.

## Corrections to mathematical statements

1. `paper/sections/introduction.tex:86` says that Theorem B sums over
   **acyclic orientations**. It must say **admissible orientations**, meaning
   that the graph of strict and ascending edges is acyclic. The orientation
   of ordinary K3 with ascending set `{13}` has directed cycle
   `1 -> 3 -> 2 -> 1` when descending edges are included, but it must occur
   in the expansion, contributing `q e_{21}`. The preliminaries correctly
   distinguish these notions. Make the same correction at line 121.

2. `paper/sections/connectivity.tex:527` applies Lemma `complete` to an
   arbitrary connected block in the last clique. That lemma requires the
   edge between the extreme vertices to be a cover. A general block need
   not meet this hypothesis. Say here only that flip paths within a block
   lift to the whole graph. Apply the complete-graph connectivity lemma
   specifically to the block containing `a,e`, where the cover `ae` supplies
   the hypothesis, as in the subsequent construction. This is an overbroad
   assertion in the exposition, not a demonstrated failure of the construction.

3. At `connectivity.tex:502`, the core has the same corners but not literally
   the same corner chains: deleting vertices in `(c,e)` removes singleton
   chains. Replace by “the same corners, and the same terminal labels on the
   retained vertices.” The argument only uses this restricted statement.

One small definition completion: at `circular.tex:54`, explicitly extend
`chi(theta,F)` by zero for `F` not contained in `theta`, as well as for
unbalanced `F`; the unrestricted sum defining `a_C` uses this extension.

## Claims about formalization and author-requested material

`introduction.tex:125` claims that **all results of the paper** were formally
verified. The recorded Lean scope includes the ordinary and circular component
identities and elementary expansions, but not the cumulant corollary; no
cumulant development is present in the Lean sources. A precise replacement is:

> The ordinary and circular component identities and their elementary
> expansions have been formally verified in Lean using Mathlib.

Keep the repository link. This positive scope statement needs no added caveat
about the published cumulant theorem. The author-requested AI assistance
statement is also absent from `paper/`; the earlier approved text remains in
`docs/drafts/AI_STATEMENT.md` and can be carried over.

The original four AS22 relations are no longer displayed together. The new
proof uses NN and DN, derives them directly, and handles ND/DD by changing a
strict marking. That dependency is sound. A compact, attributed display of
the original corner/NN/DN/ND relations, with eligibility hypotheses and the
parameter shift, would still satisfy the author's earlier explicit request
and explain the relation to AS22 without restoring the discarded proof route.

## Figures and presentation

The HRV walkthrough and eight-orientation example make the definitions more
concrete. The new source still uses many ytableau pictures, including the
generic NN/DN contact figure, rather than the requested sparse TikZ path
diagrams. The contact figure does not distinguish arbitrary intervening
intervals from the consecutive pair `x,y`. Figure 2's flip labels are small
and pale at print size. These are presentation follow-ups, not mathematical
objections to the examples.

At `preliminaries.tex:439`, remove “For all these classes, a computer check
confirms Theorem ...”. The statistics table may illustrate class sizes, but
finite checks are not supporting evidence needed for this proved theorem.
The enumeration table was not independently recomputed in this review.

## Verification

Built an isolated `git archive` snapshot with `latexmk -pdf
-interaction=nonstopmode -halt-on-error main.tex`. The 33-page PDF compiles
with no warnings, overfull boxes or underfull boxes. All 79 labels are unique
and all 156 references resolve. The source contains actual theorem, lemma,
proposition, definition and proof environments. Inspected rendered pages 7
and 12 for the large class example and contact diagrams.

Temporary build and rendered pages: `/tmp/llt-paper-review.FzxFxl/paper/`.
The ordinary review covered the local identity, three corrections, isolation,
marked endpoint attachment, connectivity and lexicographic induction. The
circular review covered finite cancellation, coefficient constancy, compatible
lifts, the union of ordinary classes, and the cumulant deduction. No manuscript
or Lean source was changed, and no print job was submitted.
