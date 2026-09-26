# Ordinary expansion completion audit

The goal is the ordinary Alexandersson–Sulzgruber combinatorial elementary
expansion, with a minimal faithful finite-degree interface. The checked main
theorem quantifies over every valid path and every finite alphabet; it has
no recurrence, orientation matching, or expansion hypothesis.

| Requirement | Authoritative evidence |
| --- | --- |
| Independent architecture review before scaffolding | `81b4885`, `docs/FORMALIZATION.md`; independent Astra reviewer and primary source/API audit recorded before Lake package creation. |
| Faithful coloring semantics | `Coloring.lean`: finite admissible colorings, strict-edge inequalities, normal-edge ascent count, vertex monomials. |
| Independent orientation semantics | `Orientation.lean`, `HRV.lean`, `OrientationExpansion.lean`: normal-edge choices, strict/ascending reachability, maximum, fiber elementary product. |
| Proved coloring recurrence | `coloringLLT_satisfiesRecursion` and `coloringLLT_satisfiesReductionRecursion`. |
| Proved orientation recurrence | `orientationExpansion_satisfiesReductionRecursion`; unrestricted NN/DN identities with actual proved bijections and HRV transport. |
| Termination and uniqueness | Three generalized bounce packages and `SatisfiesReductionRecursion.unique`, using size/east-count/height decrease certificates. |
| Ordinary semantic bridge | `coloringLLT_eq_eval_orientationExpansion`, `coloringLLT_eq_orientation_sum` in `Expansion.lean`. |
| Shifted source formula | `coloringLLT_shifted_eq_orientation_sum`; `xQShift` is coefficient substitution X→X+1. |
| Elementary positivity | `shiftedOrientationExpansion_coeff_nonneg` and `coloringLLT_shifted_e_positive`: all elementary monomials and all q-coefficients. |
| Finite degree | `orientationExpansionAt_isWeightedHomogeneous_degree`: weight k on e_k, total n. |
| Alphabet compatibility | `specializeTail_coloringLLT`: every path, alphabet size m, and number k of extra variables set to zero. |
| Local trusted verification | Default `lake-workspace build`, 1668 jobs; 438 axiom checks, only standard Lean axioms; source/line-width guards pass. |
| Repository preservation | Initial commits `830cc6b`, `130f7e8` remain ancestors; references unchanged from `130f7e8`; private repository and original remotes retained. |
| Modular delegation and build ownership | `HANDOFF.md` history records disjoint Luna/Terra files and read-only audits; primary alone ran serialized local builds. |
| External proof provenance | `docs/ARISTOTLE.md` records completed isolated jobs, fidelity checks, and authoritative local ports. |

The stronger sufficient certificate is an intentional proof route, recorded
before implementation. Original restricted-recursion uniqueness is not proved
or assumed. The concrete main formula is not conditional on that claim.
The earlier recursive-invariant plan was superseded by direct uniqueness;
defining a recursive object was never used as evidence of semantic equality.

The uniform finite-alphabet family and specialization compatibility are the
chosen representation of the ordinary identity. An abstract symmetric-function
object, a general symmetric-functions library, circular LLTs, cumulants, and
flip-component work are outside this completed scope.

Verification logs are external:
`/lake-cache/ai-projects/build/VerticalStripLLT/completion-full-build.log` and
`completion-axioms.log`. The final pushed source checkpoint is recorded in
`HANDOFF.md`; generated output and remote request archives are not committed.
