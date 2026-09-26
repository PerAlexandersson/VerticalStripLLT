import VerticalStripLLT.Circular.ChainSingletonReduction
import VerticalStripLLT.Circular.ChainSingletonSelection

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace VerticalStripLLT.Circular.ChainSingletonData

/-- The actual circular HRV expansion for an arbitrary strict chain plus one isolated vertex. -/
theorem coloringLLT_shifted_eq_expansion {n k : ℕ} {D : Diagram n}
    (S : ChainSingletonData D k) (m : ℕ) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  classical
  rw [S.eval_expansion_reduce m]
  have hext : (∑ A ∈ (S.outEdges ∪ S.inEdges).powerset,
      (MvPolynomial.C Polynomial.X : XPoly m) ^ A.card * evalElementary m (D.orientMono A)) =
      ∑ U ∈ (S.outEdges.image (fun e => S.chainIdx e.tail)).powerset,
        ∑ V ∈ (S.inEdges.image (fun e => S.chainIdx e.head)).powerset,
          (MvPolynomial.C Polynomial.X : XPoly m) ^ (U.card + V.card) *
            selectionValue k m U V := by
    rw [← ChainSingletonSubsets.sum_powerset_union_image S.outEdges S.inEdges S.disjoint_out_in _ _
      S.injOn_outEdges S.injOn_inEdges (selectionValue k m)]
    apply Finset.sum_congr rfl
    intro A hA
    rw [S.eval_orientMono_external (Finset.mem_powerset.mp hA) m]
  have hOI : ∀ i : Fin k, i.succ ∈ Finset.univ.filter S.incoming ↔
      i.castSucc ∈ Finset.univ.filter S.outgoing := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact S.incoming_succ_iff i
  rw [hext, S.image_outEdges, S.image_inEdges]
  unfold selectionValue
  rw [ChainSingletonComb.selection_sum _ _ hOI, S.xQShift_coloringLLT_closed m, S.sum_gapEps m,
    S.card_outgoing_erase_last]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold baseAscentCount
  rw [map_pow, map_add, map_one, add_comm (MvPolynomial.C Polynomial.X) 1, pow_add]
  ring

end VerticalStripLLT.Circular.ChainSingletonData
