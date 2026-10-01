import VerticalStripLLT.Components.WordProof.ComponentExpansion
import VerticalStripLLT.Components.WordProof.BlockListCancellation
import VerticalStripLLT.Components.WordProof.BlockTailFactorization
import VerticalStripLLT.Components.WordProof.MountainProduct
import VerticalStripLLT.Components.WordProof.OrderedBlockHRV

/-!
# The component theorem by words

An independent, earlier proof of the ordinary component theorem. A component
count on compatible words descends to a linear functional on the word quotient,
and a signed mountain-word scan with block cancellation extracts the HRV sum
(`docs/proofs/COMPONENT_ORDINARY_PROOF.md`).

* `OrdinaryComponentExpansion`: `component_strict_eq_elementary_of_forward_by_words`.
* `ComponentExpansion`: `component_strict_eq_elementary_by_words` and its weighted and
  e-positive forms, via the circular companion reduction.

The diagram proof (`VerticalStripLLT.Components.DiagramProof`) imports none of
these modules. The last four imports are auxiliary block and mountain lemmas
that are not used by the theorems above.
-/
