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

The coloring sums and highest-reachable-vertex expansions are defined
independently and proved equal for every finite alphabet, including the empty
alphabet. The diagram and word proofs of the component theorem are separate;
neither imports the other's proof directory.

The verification file checks the main theorems and their axioms. The project
uses no `sorry`, custom axioms, or proof placeholders.

## Build

Pinned to Lean **4.34.0** and the Mathlib revision in `lake-manifest.json`.
In this workspace, run sequentially with no other Lean build active:

```sh
lake-workspace build
lake-workspace env lean Verification.lean
```

The wrapper keeps build artifacts outside the checkout. See [AGENTS.md](AGENTS.md)
for workspace setup and build ownership.

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
