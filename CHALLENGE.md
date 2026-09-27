# Challenge: a shorter component proof

Find a simpler Lean proof of the ordinary or circular flip-component expansion
in [Challenge.lean](Challenge.lean). Both statements are already proved in this
repository; the challenge is to shorten the argument or its dependencies while
preserving the original semantics.

For a circular diagram D, orientation θ and finite alphabet size m, the target is

```text
sum over η in the complete flip component of θ:
  strict-coloring enumerator of η
=
elementary evaluation of the sum of η's actual HRV monomials.
```

`Challenge.lean` imports the existing definitions and names the circular and
ordinary propositions. It has no proof holes or axioms and compiles as supplied.
It is a single challenge file within this project, not a Mathlib-only bundle.
The declarations are propositions to prove, not assertions that a new proof exists.

## Rules

- Preserve the definitions of the diagram, full integer-cover flips, complete
  component, strict-coloring enumerator and highest-reachable-vertex (HRV) map.
- Prove the universal statement, including alphabet size zero. The circular
  diagram type itself requires a positive vertex count.
- Use only the usual Lean axioms: `propext`, `Classical.choice`, `Quot.sound`.
- For an independent solution, do not import the umbrella `VerticalStripLLT`,
  `Components.ComponentExpansion`, `Components.OrdinaryComponentExpansion`, or
  any equivalent final theorem through an indirect import. Existing definitions,
  Mathlib and lower-level project lemmas are allowed; disclose imports used.
- Compare proof length, dependencies and measured elaboration cost. A one-line
  application of the existing answer or a renamed intermediate is not a shortcut.

## Smaller optimization targets

| Target | Existing module | What would help |
| --- | --- | --- |
| Ordinary component identity | `Components/OrdinaryComponentExpansion.lean` | A shorter dependency chain from the actual component count to the HRV sum. |
| Per-state extraction | `Components/HRVScanExtraction.lean` | A simpler invariant or successor proof, retaining actual HRV fibers and `a 0 = 1`. |
| Circular reduction | `Components/CircularFromOrdinaryComponents.lean` | A smaller finite transport argument for a union of whole ordinary components. |

The current route is the word functional, finite Cauchy factorization and signed
sink cancellation, followed by the finite circular companion and compatible lifts.
See the [module map](docs/COMPONENT_FORMALIZATION.md) and
[completion audit](docs/COMPONENT_COMPLETION.md) for the reference solution.
The target is the finite strict/e identity; no finite-alphabet omega shortcut is assumed.

## Checking a candidate

Keep experiments outside the imported library until they pass. In this workspace,
with the single Lean build slot available, run sequentially:

```sh
lake-workspace env lean Challenge.lean
lake-workspace env lean Candidate.lean
```

Include `#print axioms` for the candidate theorem. An accepted replacement must
also pass the affected library build, the full build and `Verification.lean`.
The existing proof checkpoint is `f355a28` (full build: 2074 jobs; 2800 axiom entries).
