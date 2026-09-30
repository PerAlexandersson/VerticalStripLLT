# Keep the diagram proof's structural imports small

The cleanup audit found reusable structural interfaces in existing files
that also import word-specific machinery. For example,
`Components/ComponentSumPartition.lean` imports `ComponentCoefficient`.
Reusing that entire module for finite component grouping would obscure the
new diagram proof's dependency boundary and add unnecessary build work.

During formalization, use `Finset.sum_fiberwise` directly where sufficient.
If more existing structural declarations are needed, move them to a small
lower-level module in a focused refactor, preserving public names and
checking the affected dependents. Keep one actual flip/component model.
This is a proposal for the implementation stage, not a change made now.

See `docs/proofs/COMPONENT_DIAGRAM_AUDIT.md` for the reviewed decomposition.
