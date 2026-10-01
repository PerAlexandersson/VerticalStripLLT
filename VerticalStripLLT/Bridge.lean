import VerticalStripLLT.Bridge.ByCircular
import VerticalStripLLT.Bridge.ByComponents

/-!
# The Alexandersson–Sulzgruber expansion from the new proofs

`VerticalStripLLT.Expansion` formalizes the ordinary expansion of [AS22] along the
paper's own recursion. The bridge derives the same statements independently of that
recursion:

* `Bridge.PathRelations`, `Bridge.PathDiagram`: an ordinary Schröder path of positive
  size is the forward circular diagram `SchroderPath.toDiagram` with the same natural
  and strict relations, coloring sum and shifted HRV expansion.
* `Bridge.ByCircular`: `coloringLLT_shifted_eq_eval_shiftedOrientationExpansion_by_circular`
  and `coloringLLT_eq_eval_orientationExpansion_by_circular`, from the circular expansion.
* `Bridge.ByComponents`: `..._by_components` and
  `coloringLLT_shifted_e_positive_by_components`, from the ordinary component theorem by
  diagrams, summed over all flip components.
-/
