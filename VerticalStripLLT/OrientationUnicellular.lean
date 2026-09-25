import VerticalStripLLT.OrientationInsertSum
import VerticalStripLLT.Unicellular

namespace VerticalStripLLT

theorem orientationExpansionAt_unicellular {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) (z : Q) :
    orientationExpansionAt (SchroderPath.resolveNorthEast U V h) z -
        orientationExpansionAt (SchroderPath.resolveEastNorth U V h) z =
      MvPolynomial.C z * orientationExpansionAt
        (⟨U ++ Step.diagonal :: V, h⟩ : SchroderPath n) z := by
  set a := SchroderPath.markedDiagonalEdge U V h
  have hnot := SchroderPath.markedDiagonalEdge_not_mem_eastNorth_normalEdges U V h
  have hN := SchroderPath.northEast_normalEdges_eq_insert U V h
  have hS := SchroderPath.resolve_strictEdges_eq U V h
  have hND := (SchroderPath.resolve_diagonal_normalEdges_eq U V h).symm
  have hSD := SchroderPath.diagonal_strictEdges_eq_insert U V h
  rw [orientationExpansionAt_insert_sum a hnot hN z,
    ← orientationExpansionAt_sum_transport hND z, Finset.mul_sum]
  unfold orientationExpansionAt
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [insert_false_summand a hnot hN hS z θ,
    insert_true_summand a hnot hN hS hND hSD z θ]
  ring

end VerticalStripLLT
