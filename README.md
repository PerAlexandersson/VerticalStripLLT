# VerticalStripLLT

Lean 4 formalization accompanying Per Alexandersson and Lilan Dai,
*Flip classes and elementary expansions of vertical-strip LLT polynomials*
([manuscript](paper/llt-flip-classes.pdf)). It proves an elementary-symmetric-
function expansion for each complete flip class, for both ordinary and circular
vertical-strip LLT polynomials. Summing over classes recovers the ordinary
expansion and gives its circular analogue.

## Results

| Result | Lean entry point |
| --- | --- |
| Ordinary LLT expansion and shifted e-positivity | [Expansion.lean](VerticalStripLLT/Expansion.lean) |
| Circular LLT expansion and shifted e-positivity | [Circular/Expansion.lean](VerticalStripLLT/Circular/Expansion.lean) |
| Ordinary and circular flip-component expansions and e-positivity, by diagrams | [Components/DiagramProof.lean](VerticalStripLLT/Components/DiagramProof.lean) |
| The same component theorems by an independent word-functional proof | [Components/WordProof.lean](VerticalStripLLT/Components/WordProof.lean) |
| The ordinary expansion again, from the circular and component theorems, without the recursion of the paper | [Bridge.lean](VerticalStripLLT/Bridge.lean) |
| Cyclic Hessenberg loop LLT expansion, matching coefficient formula and e-positivity | [CyclicHessenberg.lean](VerticalStripLLT/CyclicHessenberg.lean) |

The coloring sums and highest-reachable-vertex expansions are defined
independently and proved equal for every finite alphabet, including the empty
alphabet. The diagram and word proofs of the component theorem are separate;
neither imports the other's proof directory.

The separate cyclic Hessenberg development follows the loop/coloring proof:
transfer-kernel exchange, positive root deletion, and canonical cycle and matching
expansions. Its independently defined composition source agrees with the coloring
sum. After `q ↦ q+1`, one elementary expression over `ℕ[q]` works for every finite
alphabet; each coefficient counts matchings with marked ascent events. Main source
expansion theorems assume a positive layer count and include empty support and
empty alphabets. This result does not assert a circular flip-class decomposition.
See the [source map and proof plan](docs/CYCLIC_HESSENBERG_PLAN.md) and
[public theorem interfaces](VerticalStripLLT/Challenges/CyclicHessenberg.lean).

The verification file checks the main theorems and their axioms. The project
uses no `sorry`, custom axioms, or proof placeholders.

## Build

Pinned to Lean **4.34.0** and the Mathlib revision in `lake-manifest.json`.
In this workspace, run sequentially with no other Lean build active:

```sh
lake-workspace build
lake-workspace env lean Verification.lean
lake-workspace build VerticalStripLLT.CyclicHessenberg.Audit
```

The wrapper keeps build artifacts outside the checkout. See [AGENTS.md](AGENTS.md)
for workspace setup and build ownership. In the current Docker worker, builds
run through the authorized host bridge with `--project VerticalStripLLT`; the
RealRooted Lean MCP and local/Euler builds are not used for this task.

## Further reading

- Alexandersson and Sulzgruber,
  [*A combinatorial expansion of vertical-strip LLT polynomials in the basis
  of elementary symmetric functions*](https://doi.org/10.1016/j.aim.2022.108256),
  *Advances in Mathematics* **400** (2022), 108256.
- Hwang,
  [*Chromatic quasisymmetric functions and noncommutative P-symmetric
  functions*](https://doi.org/10.1090/tran/9096),
  *Transactions of the AMS* **377** (2024), 2855–2896.
- [Challenge](CHALLENGE.md): a precise target for a shorter component proof.
- [Documentation](docs/README.md): proof maps, source correspondence and audits.
- Completion audits: [ordinary](docs/COMPLETION.md),
  [circular](docs/CIRCULAR_COMPLETION.md),
  [components by diagrams](docs/DIAGRAM_PROOF_COMPLETION.md),
  [components by words](docs/COMPONENT_COMPLETION.md).
