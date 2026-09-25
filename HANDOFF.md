# VerticalStripLLT handoff

## Current status

- General graph foundations and strict-column model now compile: both edge
  sets have increasing endpoints and are disjoint; `column k` has exactly
  consecutive strict edges, no normal edges, and admissibility `StrictMono`.
  This advances the general base case; its elementary sum identity is still
  being searched by Aristotle. Concatenation is under implementation.
- First end-to-end slice complete, 2026-09-25, on `main` in the private
  `PerAlexandersson/VerticalStripLLT` repository. Full package build and public
  axiom audit pass. The ordinary theorem as a whole is still open.
- Architecture checkpoint `81b4885` was committed and pushed before any
  scaffolding. See `docs/FORMALIZATION.md` for the independent Astra review,
  source map, representation comparison, termination measure, and milestones.
- Verified implementation checkpoint:
  `cab97ea9b353ff62772e0e154323964013d2704e`, pushed to `origin/main`.
  The subsequent handoff receipt changes documentation only.
- Model: valid `n/d/e` words, finite coloring polynomials over `Polynomial ℤ`,
  and a separate ring of formal elementary expressions with an evaluation map.
- Pinned Lean `v4.34.0`, Mathlib
  `5ed2965256430c3649e86755f9576b54eca72435`; dependency closure is tracked.
- Primary `/root` remains strategy, source, integration, and sole build owner.
  No build is running. Active assignments below supersede the completed-slice
  ownership record while this increment is in progress.

## Active continuation

- Previous turn: progress (reviewed architecture and verified first slice).
- User requests continued work on the full ordinary expansion, with Luna doing
  most implementation and Aristotle used whenever useful. Goal remains active.
- Primary owns integration, docs, verification, Aristotle job preparation and
  monitoring, and the sole build slot.
- Luna `path_invariants` completed `PathInvariants.lean`; primary compiled it,
  adopted it, and removed unused simp arguments. No file currently delegated
  to that worker. Public raw scanner lower-bound lemmas were retained for
  later graph concatenation proofs.
- `Column.lean` is now compiled and returned to primary for integration.
  Luna `column_paths` next owns only new `VerticalStripLLT/Concat.lean`,
  implementing the six raw append/translation laws and path concatenation.
- Other project files and immutable references are not delegated.
- Milestone issue: https://github.com/PerAlexandersson/VerticalStripLLT/issues/1.
- Aristotle CLI is available despite absence from MCP. The general increasing
  coloring / elementary identity is running as project
  `262ce79f-3c8a-4e6a-83f7-6fcf6a6c9eb6`; exact task, request paths, environment
  mismatch, and a capacity-rejected second request are in `docs/ARISTOTLE.md`.

New exact public interfaces are `Step.normalFrom_lower_bound`,
`Step.strictFrom_lower_bound`, `Step.normalFrom_lt`,
`Step.strictFrom_lt_of_valid`, `Step.normalFrom_strictFrom_disjoint`,
`SchroderPath.normalEdges_lt`, `strictEdges_lt`,
`normalEdges_disjoint_strictEdges`, `column`, `column_normalEdges`,
`column_strict_mem_iff`, `column_strictEdges`, `column_ascentCount`, and
`admissible_column_iff`. Namespace is `VerticalStripLLT` throughout.

Build discipline improvement: commands now abort if the process guard sees
any Lean/Lake process. An initial continuation check displayed two short-lived
processes that had exited by the immediate follow-up inspection; ownership
could not be reconstructed. No other worker was stopped or reconfigured.

Graph/column checkpoint checks: focused build of `PathInvariants` and `Column`,
then full/default build (1360 jobs), and `Verification.lean` all passed. The
18 audited declarations use only the standard axioms; the new files are free
of placeholders. Axiom log is
`/lake-cache/ai-projects/build/VerticalStripLLT/graph-column-axioms.log`.
Untracked `Concat.lean` is a separate active candidate and is excluded from
this verified checkpoint and root imports until its focused check passes.

## Completed declarations

All names are in namespace `VerticalStripLLT`.

| File | Declarations and verified scope |
| --- | --- |
| `VerticalStripLLT/Path.lean` | `Step`, `Step.validFrom`, `Step.normalFrom`, `Step.strictFrom`, `SchroderPath`; empty/singleton/strictPair/normalPair/disconnectedPair paths and their exact edge-set lemmas. |
| `VerticalStripLLT/Polynomial.lean` | `Q`, `XPoly`, `EExpansion`, `elementary`, `evalElementary`, `evalElementary_C`, `evalElementary_elementary`. |
| `VerticalStripLLT/Coloring.lean` | `admissible`, `ascentCount`, `coloringWeight`, `coloringLLT`; directly defined from finite colorings, independently of recursion. |
| `VerticalStripLLT/SmallCases.lean` | `coloringLLT_empty`, `coloringLLT_singleton`, `coloringWeight_pair_relation`, `coloringLLT_pair_unicellular`: all finite alphabets, including zero. |
| Same | `coloringLLT_strictPair_two`, `coloringLLT_normalPair_two`, `coloringLLT_disconnectedPair_two`: explicit two-variable polynomials. |
| Same | `coloringLLT_strictPair_eq_evalElementary_two`, `normalPairExpansion`, `coloringLLT_normalPair_eq_evalElementary_two`: two-variable semantic identities `G_nde=e₂` and `G_nnee=e₁²+(q−1)e₂`. |

There is no general recursive invariant yet. The last two identities are small
semantic bridges, not the full ordinary expansion or orientation theorem.

## Verification

Primary checked the process list for active Lean/Lake processes before each
build; none from other projects were active. All commands ran sequentially
through `lake-workspace` with a 20-minute bound and reduced CPU priority.

- Focused `lake-workspace build VerticalStripLLT.SmallCases`: passed.
- Full/default `lake-workspace build`: passed (1321 jobs, mostly cached).
- `lake-workspace env lean Verification.lean`: passed. All 11 audited public
  declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.
- Source scan: no `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide`.
- `git diff --check` and Lean line-width check (100 columns): passed.
- Reference snapshot unchanged relative to `130f7e8`.
- No project-local `.lake/packages` or `.lake/build`; outputs are external.
- Logs: `/lake-cache/ai-projects/build/VerticalStripLLT/first-slice-build.log`
  and `first-slice-axioms.log` in the same directory.

The wrapper's temporary external package override emits a manifest
packages-directory warning. It is expected, does not invalidate these checks,
and is not an instruction to update dependencies. Do not run plain Lake.

## Review and ownership record

- Astra `/root/architecture_review`: completed independent planning before
  architecture/scaffolding, then a read-only audit of the compiled path decoder
  and theorem scope. No semantic blocker found; no edits or builds.
- Luna `/root/finite_sum_api`: bounded read-only Mathlib API audit after the
  architecture commit. Returned finite-function sum equivalences and elementary
  polynomial API notes; no edits or builds. Primary checked and integrated the
  useful suggestions locally.
- Primary authored all source/configuration/documentation and owns the entire
  project source lane. Reference files remain immutable. No build-slot transfer.

## Next step and remaining obligations

Next bounded milestone: prove graph-edge orderedness/disjointness, formalize
path concatenation and its coloring identity, and extend the strict-chain
base case `n d^k e = e_(k+1)` to arbitrary finite alphabets.

Subsequent work: general unicellular and bounce identities; bounce reduction;
lexicographic decrease lemmas for `(size, east-step count, first-east height)`;
recurrence uniqueness; the terminating elementary invariant and named coloring
bridge; independent orientation/HRV expression and its recurrence; expansion,
shifted positivity, degree preservation, and finite-alphabet stability.

The source's `F_ne=1` sentence is a typo: we use `e₁`. Source division by
`q−1` must become justified cancellation in the integral coefficient model.
Formal expression evaluation in a fixed small alphabet is not assumed injective.
Circular LLTs, cumulants, and flip-component work have not begun.

## Repository and tools

- Preserved initialization commits: `830cc6b` and `130f7e8`.
- Runtime registry and `codex mcp list` inspected. Lean MCP local search works
  with an explicit Mathlib root, but its default server starts in RealRooted;
  avoid build/LSP commands that could target that package. See the project
  suggestion in `suggestions/project-tool-routing.md`.
- AXLE is available but was unnecessary for this slice. Aristotle is not
  exposed in the runtime registry. No auxiliary proof-service requests were made.
- Rust capability audit is recorded in `docs/FORMALIZATION.md`; no external
  computation code or Rust changes were needed.
- SSH remote authentication is unavailable here. Read and push via an
  invocation-local HTTPS rewrite and the existing GitHub credential helper:

  ```bash
  git -c url.https://github.com/.insteadOf=git@github.com: \
    -c credential.helper= -c 'credential.helper=!gh auth git-credential' \
    push origin main
  ```

  The configured remote remains unchanged. No credentials are stored here.

## Authoritative manuscript

The author-supplied regular-file snapshot lives under
`references/alexandersson-sulzgruber-2022/`. The formalization map uses Theorem
`recursion`, Theorem `LLT`, Theorem `LLTe`, and Corollary `expansion` in
`main.tex`. The original host source is
`/home/paxinum/Dropbox/research-finished/GIT-LLT-e-Robin/LLT-E-expansion-bijective-proof`;
Docker cannot access that mount. Do not edit the committed reference snapshot.
