# VerticalStripLLT agent guide

Read `/workspace/AGENTS.md`, `/workspace/lean/AGENTS.md`, this file, and
`HANDOFF.md` before editing or building.

## Scope

The ordinary Alexandersson--Sulzgruber expansion is complete. The user then
authorized the circular development; its aggregate HRV formula is also proved.
See `docs/CIRCULAR_COMPLETION.md`. Ordinary and balanced circular flip-component
expansions now have audited mathematical proofs, pending Lean integration;
primitive unbalanced circular components remain open. See
`docs/proofs/COMPONENT_ORDINARY_PROOF.md`. Retain the faithful finite-degree
model; do not build a general symmetric-functions library without an explicit demonstrated need and user
approval.

The target mathematical source is arXiv:2004.09198 and its published version.
Use the local paper cache when available. Record precise theorem/definition
correspondence in the handoff or dedicated source map.

## Ownership and delegation

The primary Astra worker is the strategy, integration, source-ownership, and
serialized-build owner. Before settling the architecture, it must obtain an
independent Astra-level review of the representation and proof decomposition
and record the resulting decision.

The primary worker may delegate small, bounded, independent implementation or
API-audit tasks to Luna subagents. Assign disjoint files and record ownership
in `HANDOFF.md` before edits. Luna subagents must return focused commits or
notes to the primary owner and must not broaden scope.

Only the primary worker may invoke Lake or other Lean builds. Subagents may
inspect and edit their assigned files but remain build-free unless the primary
worker explicitly transfers the single build slot after recording that change.
All large builds remain serialized with every other Lean project.

## Formalization strategy

Prefer explicit finite combinatorial models:

- decorated area sequences / `n`, `d`, `e` path data;
- packed-coloring or fixed-degree coefficient semantics;
- finitely supported elementary-basis expansions over `Polynomial ℤ`;
- deterministic recursion with an explicit well-founded measure;
- a separate theorem identifying the recursive object with the coloring LLT.

Do not call an object the usual LLT polynomial solely because it was defined by
the recurrence. Preserve the semantic bridge as a named milestone.

Keep the ordinary theorem independent of circular and flip-component arguments.
Keep the proved aggregate circular theorem independent of the unresolved
flip-component expansion; aggregate positivity does not prove component positivity.

## Lean workflow

Use `lake-workspace`, never plain Lake, once the project is configured. Keep
build products under `/lake-cache/ai-projects`. Run focused checks before a
full build. Follow the shared Lean style, including `lia` rather than `omega`.

Commit and push coherent verified checkpoints. Update `HANDOFF.md` with exact
ownership, decisions, checks, blockers, branches, and commit hashes.
