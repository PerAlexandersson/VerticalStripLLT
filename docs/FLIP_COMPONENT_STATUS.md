# Flip-component proof status

**Complete in Lean.** The ordinary and full circular component strict/e
identities, common shifted q-weights, elementary positivity and weighted degree
are proved for actual complete flip components. The final library passes
2074 jobs and 2800 axiom inventory entries, using only the standard axioms.
See [the completion audit](COMPONENT_COMPLETION.md) and
[the module map](COMPONENT_FORMALIZATION.md).

The ordinary proof uses the actual component word functional, finite Cauchy
factorization and direct signed-sink extraction. The circular proof uses the
finite companion and compatible lifts. Its ordinary preimage is a union of
complete components, so reverse flip transport is unnecessary. Aggregate
expansions are not used to infer component identities.

## Mathematical sources

- [Ordinary word proof](proofs/COMPONENT_ORDINARY_PROOF.md).
- [Overleaf v9 comparison](proofs/COMPONENT_CIRCULAR_FACE_PROOF.md): the source
  of direct extraction and the alternative bounded-face circular proof.
- [Finite companion](proofs/COMPONENT_FINITE_COMPANION.md): the integrated
  finite replacement for the polyhedral argument, including component isolation.
- [Circular interfaces](CIRCULAR_FLIPS.md): exact full-cover flips and components.

The public result is finite strict/e; the manuscript uses weak/h conventions.
No finite-alphabet omega translation is claimed. All finite alphabets, including
zero, are covered. Circular Diagram n requires n>0, so no empty-vertex component
is represented by these declarations.

## Historical alternatives

The [periodic word audit](proofs/COMPONENT_PERIODIC_WORDS.md) rules out extending
the ordinary four-word quotient unchanged. The verified proof needs no such
extension. Older DN packet isolation, active uniqueness, saturation and
closure-fiber assertions remain separate auxiliary claims; the theorem neither
assumes nor automatically proves them.

The [earlier status archive](archive/component-status-before-ordinary-word-proof.md)
and [integration history](archive/component-integration-through-scan-20260927.md)
preserve failed shortcuts and alternative approaches. They are not active proof
obligations. Current ownership and verification belong in [HANDOFF](../HANDOFF.md).
Cumulants and manuscript rewriting remain outside this task.
