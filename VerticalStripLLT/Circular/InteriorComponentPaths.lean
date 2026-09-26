import VerticalStripLLT.Circular.InteriorResidualTransport
import VerticalStripLLT.Circular.DNTargetPairs

/-! Total comparability of vertices in an isolated strict component. -/

namespace VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

open scoped Classical

variable {n r j : ℕ} {D : Diagram n} {t : ℤ}
  (K : InteriorMergedComponent D t r j)

theorem strict_path_of_index_lt (a b : ℕ) (hb : b < r + j) (hab : a < b) :
    Relation.TransGen (D.edgeData.selected ∅) (K.vertex a) (K.vertex b) := by
  induction b generalizing a with
  | zero => lia
  | succ b ih =>
    by_cases heq : a = b
    · subst a
      exact Relation.TransGen.single (K.step b (by lia))
    · have hab' : a < b := by lia
      exact (ih a (by lia) hab').tail (K.step b (by lia))

theorem component_strict_total (u v : Fin n)
    (hu : u ∈ K.componentVertices) (hv : v ∈ K.componentVertices)
    (hne : u ≠ v) :
    Relation.TransGen (D.edgeData.selected ∅) u v ∨
      Relation.TransGen (D.edgeData.selected ∅) v u := by
  obtain ⟨a, ha⟩ := (K.mem_componentVertices_iff u).mp hu
  obtain ⟨b, hb⟩ := (K.mem_componentVertices_iff v).mp hv
  by_cases hab : a.val < b.val
  · left
    rw [← ha, ← hb]
    exact K.strict_path_of_index_lt a.val b.val b.isLt hab
  · right
    have hba : b.val < a.val := by
      have hne' : a.val ≠ b.val := by
        intro heq
        apply hne
        exact ha.symm.trans ((congrArg K.vertex heq).trans hb)
      lia
    rw [← ha, ← hb]
    exact K.strict_path_of_index_lt b.val a.val a.isLt hba

private theorem target_path_of_source_path {u v : Fin n}
    (h : Relation.TransGen (D.edgeData.selected ∅) u v) :
    Relation.TransGen
      (K.reversalTarget.edgeData.selected ∅)
      (K.reversalPerm u) (K.reversalPerm v) := by
  exact Relation.TransGen.lift K.reversalPerm
    (fun u v huv => (K.reversalTarget.selected_empty_iff_pair_strict _ _).mpr
      ((K.strictPairs_reversal_iff u v).mpr
        ((D.selected_empty_iff_pair_strict u v).mp huv))) _ _ h

theorem reversalTarget_component_strict_total (u v : Fin n)
    (hu : u ∈ K.componentVertices) (hv : v ∈ K.componentVertices)
    (hne : u ≠ v) :
    Relation.TransGen (K.reversalTarget.edgeData.selected ∅) u v ∨
      Relation.TransGen (K.reversalTarget.edgeData.selected ∅) v u := by
  have hu' : K.reversalPerm u ∈ K.componentVertices :=
    (K.reversalPerm_mem_component_iff u).mpr hu
  have hv' : K.reversalPerm v ∈ K.componentVertices :=
    (K.reversalPerm_mem_component_iff v).mpr hv
  have hne' : K.reversalPerm u ≠ K.reversalPerm v := by
    intro h
    exact hne (K.reversalPerm.injective h)
  rcases K.component_strict_total _ _ hu' hv' hne' with h | h
  · left
    simpa only [K.reversalPerm_involutive u, K.reversalPerm_involutive v] using
      K.target_path_of_source_path h
  · right
    simpa only [K.reversalPerm_involutive u, K.reversalPerm_involutive v] using
      K.target_path_of_source_path h

end VerticalStripLLT.Circular.Diagram.InteriorMergedComponent
