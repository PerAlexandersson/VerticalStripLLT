# Proposed writing-skill additions from the author's review

The 2026-10-01 author review exposed a mismatch between the prior manuscript
pass and the author's LLT papers. The earlier pass used shading to distinguish
weights, drew generic relations as fixed small paths, and gave proof stages
names that added unnecessary vocabulary. It also left the induction strategy
until the end of long proofs.

For a future writing-skill update, compare this revision with
`draft-v1-before-author-edits` and retain these explicit author preferences:

- Inspect the author's actual TikZ sources first. The Robin-paper snapshot
  here has provenance in references/alexandersson-sulzgruber-2022/SOURCE.md.
- Shade outside the path; do not reuse shading for q-weights. Draw consecutive
  vertices consecutively and use continuation marks for arbitrary intervals.
- Use typewriter n/e/d for literal steps. Distinguish collections, graphs,
  and evaluations by established fonts and roles, not extra letter names.
- Avoid indices and proof-stage terminology when a picture, short expression,
  or the condition itself is clearer.
- State the main results and define flips in the introduction, with a worked
  component illustrating the elementary coefficients.
- State the original recurrences before adapting them. Explain equivalence,
  orientation, initial cases, and the exact decreasing quantities before
  beginning the long local verifications.
- Give a lengthy connectivity construction its own section after stating
  exactly what it supplies to the component recurrence. Keep the diagram
  proof in the paper.

This is a proposal for later skill maintenance, not a change to skill policy.
