# VerticalStripLLT handoff

## Current status

- Project created 2026-09-25 for a Lean formalization of the ordinary
  Alexandersson--Sulzgruber vertical-strip LLT elementary expansion.
- Initial visibility: private GitHub repository.
- No Lean package, representation, or toolchain has yet been chosen.
- No Lake build has been run.
- Primary owner to be assigned: one Astra orchestrator.
- Required first action: independent Astra architecture review, followed by a
  written milestone plan. Bounded Luna implementation tasks may begin only
  after file ownership is recorded here.

## Initial milestones

1. Map the paper's definitions, recurrences, and main theorem to proposed Lean
   declarations and identify the minimal Mathlib dependencies.
2. Decide between packed-coloring coefficients, fixed-variable polynomials,
   and an elementary-basis free module; document the semantic bridge.
3. Scaffold the Lean package and prove small representation sanity lemmas.
4. Formalize ordinary decorated paths/area sequences and deterministic
   recursion with a well-founded measure.
5. Prove agreement with the coloring definition and then the orientation/HRV
   elementary expansion.
6. Expose a stable downstream API for LLT cumulants and the circular project.

## Ownership

No files are currently delegated. The primary Astra worker owns integration
and the sole project build slot once launched.
