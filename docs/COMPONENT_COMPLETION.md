# Complete flip-component expansion

The ordinary and full circular component identities are Lean theorems. The final
library build passes **2074 jobs**, and **2800 axiom inventory entries** use only
`propext`, `Classical.choice`, and `Quot.sound`. There are no proof placeholders,
custom axioms or unchecked native proofs.

## Public statements

In namespace `VerticalStripLLT.Circular`:

| Declaration | Statement |
| --- | --- |
| `component_strict_eq_elementary_of_forward` | Actual component strict-coloring sum equals its HRV elementary expression for forward diagrams. |
| `component_strict_eq_elementary` | The same identity for every circular diagram and complete flip component. |
| `component_weighted_strict_eq_orientation_sum` | The identity with each state's shifted weight `q ^ η.val.card` exposed on both sides. |
| `component_weighted_strict_eq_eval` | The weighted coloring sum evaluates the independently defined `weightedComponentHRV`. |
| `component_weighted_e_positive` | One elementary expression works for every finite alphabet, has nonnegative q-coefficients, and has elementary weighted degree n. |

The ordinary theorem is in
[OrdinaryComponentExpansion](../VerticalStripLLT/Components/OrdinaryComponentExpansion.lean).
The general theorem and corollaries are in
[ComponentExpansion](../VerticalStripLLT/Components/ComponentExpansion.lean).
All declarations are imported by the main library and listed in `Verification.lean`.

The component is the existing `flipComponent D θ`, defined by full global flip
reachability. Both valuations retain their original definitions. No balance,
connectivity, saturation, recurrence or component-isolation hypothesis remains.
The common q-exponent counts selected **normal** edges; strict edges do not
contribute to it. Alphabet size zero is included. The circular `Diagram n` model
requires `0 < n`; these statements do not represent an empty-vertex component.

## Checked proof route and source correspondence

1. The actual component count on full compatible words satisfies the contextual
   four-word relation by actual flips. It descends to a linear functional on the
   word quotient (`ComponentFunctional`).
2. Finite Cauchy factorization is paired with this functional, and then with a
   literal mountain-word scan (`ColorProductPairing`, `MountainScanPairing`,
   `ComponentScanSemantics`). Per-state compatibility is evaluated on literal
   words; it is not assumed to descend to the quotient.
3. For each actual forward orientation, induction on the HRV threshold support
   `{v | (hrv v).val < k}` extracts the product of its actual fiber weights.
   Signed first-block cancellation leaves precisely the next fiber. A nonroot
   has empty fiber, and the explicit hypothesis `a 0 = 1` removes that factor
   (`HRVBlockContinuation`, `HRVScanExtraction`). This finishes the ordinary
   strict/e identity, independently of the circular reduction.
4. The finite circular companion, coefficient constancy, whole-component
   undecoration and balanced-potential propagation reduce to balanced components.
   Compatible lift sorting constructs an ordinary diagram. Its preimage is a
   union of complete ordinary components; only forward flip transport is needed
   (`CircularFromOrdinaryComponents`). The ordinary theorem discharges the last
   hypothesis of that reduction.
5. Constant ascent number restores the q-weight. Natural-coefficient lifts and
   the actual HRV fiber sizes give positivity and weighted degree
   (`ComponentPositive`).

The source is the [ordinary word proof](proofs/COMPONENT_ORDINARY_PROOF.md), the
v9 direct signed-sink extraction described in the
[Overleaf comparison](proofs/COMPONENT_CIRCULAR_FACE_PROOF.md), and the
[finite companion](proofs/COMPONENT_FINITE_COMPANION.md). The general polyhedral
bounded-face argument is not formalized. The finite strict/e statement corresponds
to the manuscript's weak/h convention; no finite-alphabet omega translation is
claimed. The aggregate LLT theorems remain separate from this component proof.

## Verification and implementation provenance

Primary retained source integration and the sole serialized Lean build slot.
Luna supplied bounded implementation/API modules, including component positivity.
Astra supplied bounded modules and independently audited the representation,
ordinary extraction, circular transport and public statements. The independent
shorter-route review removed reverse flip transport and the ordered-partition
bijection. Claude supplied `HRVScanExtraction.lean` through file tools only;
the candidate passed its first local project build and an independent Astra
semantic review. No auxiliary process remains active.

Pinned environment: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Commands, run sequentially:

```sh
lake-workspace build VerticalStripLLT.Components.ComponentExpansion
lake-workspace build
lake-workspace env lean Verification.lean
```

Logs are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/circular-continuation/`:
`component-expansion-build.log`, `component-completion-library-build.log`, and
`component-completion-axioms.log`. Source guards, the four new modules' 100-column
checks, and `git diff --check` pass. Existing linter/deprecation warnings remain;
there are no build errors. Cumulants and general symmetric-function infrastructure
remain outside scope.
