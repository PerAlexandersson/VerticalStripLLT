import VerticalStripLLT.Circular.CornerDeleteOrientation
import VerticalStripLLT.Circular.CornerMeasure
import VerticalStripLLT.Circular.DDRecurrences

/-! A two-corner recursive exit, with the geometric measure made explicit. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

theorem expansion_of_two_nonstrict_corners {n : ℕ} (T : Diagram n) (a : ℕ)
    (harea : T.doubledArea ≤ a + 1) (e f : Edge T.area) (he : IsCorner e)
    (hf : IsCorner f) (hne : e ≠ f) (hens : e ∉ T.strict) (hfns : f ∉ T.strict)
    (m : ℕ)
    (ih : ∀ Q : Diagram n, Q.doubledArea < a →
      xQShift m (Q.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion Q)) :
    xQShift m (T.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion T) := by
  let S := T.strictify e he
  let Q := T.deleteCorner e he
  have hfS : f ∉ S.strict := by
    intro h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact hne rfl
    · exact hfns h
  have hS : S.doubledArea + 1 = T.doubledArea :=
    T.strictify_doubledArea e he hens
  have hQ : Q.doubledArea + 2 = T.doubledArea :=
    T.deleteCorner_doubledArea e he hens
  have hUf : IsCorner f := hf
  let U := S.strictify f hUf
  let V := S.deleteCorner f hUf
  have hU : U.doubledArea < a := by
    have h := S.strictify_doubledArea f hUf hfS
    lia
  have hV : V.doubledArea < a := by
    have h := S.deleteCorner_doubledArea f hUf hfS
    lia
  have hQ' : Q.doubledArea < a := by lia
  have hT := T.xQShift_coloringLLT_corner e he hens m
  have hS := S.xQShift_coloringLLT_corner f hUf hfS m
  have hTo := T.shiftedOrientationExpansion_corner e he hens
  have hSo := S.shiftedOrientationExpansion_corner f hUf hfS
  have ihU := ih U hU
  have ihV := ih V hV
  have ihQ := ih Q hQ'
  rw [hT, hS, hTo, hSo]
  simp only [map_mul, map_add, evalElementary_C]
  rw [ihU, ihV, ihQ]

/-- Two nonstrict corners in a resolved DD child close its outer area-induction step. -/
theorem DDLocalData.expansion_of_resolved_two_corners
    {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.DDLocalData t)
    (e f : Edge B.resolved.area) (he : IsCorner e) (hf : IsCorner f)
    (hne : e ≠ f) (hens : e ∉ B.resolved.strict) (hfns : f ∉ B.resolved.strict)
    (m : ℕ)
    (ih : ∀ Q : Diagram n, Q.doubledArea < D.doubledArea →
      xQShift m (Q.coloringLLT m) =
        evalElementary m (shiftedOrientationExpansion Q)) :
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D) := by
  apply B.expansion_of_resolved m ?_ ih
  exact B.resolved.expansion_of_two_nonstrict_corners D.doubledArea
    (by rw [B.resolved_doubledArea]) e f he hf hne hens hfns m ih

end VerticalStripLLT.Circular.Diagram
