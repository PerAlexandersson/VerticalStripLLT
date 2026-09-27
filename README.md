# VerticalStripLLT

Lean 4 proofs of the elementary-basis expansion of vertical-strip LLT
polynomials, its circular extension, and the expansion of every complete
flip component. The ordinary result formalizes Alexandersson–Sulzgruber,
*A combinatorial expansion of vertical-strip LLT polynomials in the basis of
elementary symmetric functions* (arXiv:2004.09198).

## Results

| Result | Lean entry point |
| --- | --- |
| Ordinary LLT expansion and shifted e-positivity | [Expansion.lean](VerticalStripLLT/Expansion.lean) |
| Circular LLT expansion and shifted e-positivity | [Circular/Expansion.lean](VerticalStripLLT/Circular/Expansion.lean) |
| Ordinary and circular flip-component expansions and e-positivity | [Components/ComponentExpansion.lean](VerticalStripLLT/Components/ComponentExpansion.lean) |

The coloring sums and highest-reachable-vertex (HRV) expansions are defined
independently. Their equality is proved for every finite alphabet, including
the empty alphabet. The circular diagram model requires a positive vertex count.
The component result uses the finite strict/e convention.

**Verified:** 2,074 build jobs and 2,800 axiom inventory entries; only
`propext`, `Classical.choice` and `Quot.sound`. No proof placeholders or custom axioms.

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

- [Challenge](CHALLENGE.md): a precise target for a shorter component proof.
- [Documentation](docs/README.md): proof maps, source correspondence and audits.
- Completion audits: [ordinary](docs/COMPLETION.md),
  [circular](docs/CIRCULAR_COMPLETION.md), [components](docs/COMPONENT_COMPLETION.md).
