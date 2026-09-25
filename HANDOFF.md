# VerticalStripLLT handoff

## Current status

- Project created 2026-09-25 for a Lean formalization of the ordinary
  Alexandersson--Sulzgruber vertical-strip LLT elementary expansion.
- Initial visibility: private GitHub repository.
- Architecture decision is recorded in `docs/FORMALIZATION.md`: valid step
  words, finite coloring polynomials uniformly in the alphabet size, and a
  separate algebra of formal elementary expressions. Lean package not yet created.
- No Lake build has been run.
- Primary owner: `/root`, Astra orchestrator (2026-09-25); source ownership,
  integration, and sole serialized project build slot.
- Independent Astra review and primary source/API audit are complete; the
  reviewed architecture checkpoint precedes all scaffolding.

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

Primary owns all project files; references are immutable. The separate Astra
`/root/architecture_review` completed the required independent read-only
review; it owns no files and ran no builds. No implementation is delegated yet.

## Initial audit

- Clean `main` at `130f7e8`, following `830cc6b`; remote main agrees and GitHub
  visibility is PRIVATE. Both initialization commits will be preserved.
- Runtime registry and `codex mcp list` inspected. Lean MCP is registered for
  RealRooted, but read-only local search works with an explicit Mathlib root.
  Avoid its build/LSP commands for this new project; use `lake-workspace`.
- AXLE is available; Aristotle is not exposed in the runtime registry.
- Existing compatible cache: Lean 4.34.0, Mathlib
  `5ed2965256430c3649e86755f9576b54eca72435`.
- SSH remote authentication is unavailable in this container. An invocation-local
  HTTPS URL rewrite with `gh auth git-credential` successfully reads remote main;
  use it for pushes without changing the configured remote or exposing credentials.

## Authoritative manuscript source

The author supplied the original source at:

`/home/paxinum/Dropbox/research-finished/GIT-LLT-e-Robin/LLT-E-expansion-bijective-proof`

Docker workers cannot access that mount directly. A regular-file snapshot of
the principal manuscript and its figure-definition files is committed under
`references/alexandersson-sulzgruber-2022/`. The main formalization map should
start from Theorem `recursion`, Theorem `LLT`, Theorem `LLTe`, and Corollary
`expansion` in `references/alexandersson-sulzgruber-2022/main.tex`.
