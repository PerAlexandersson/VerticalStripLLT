import VerticalStripLLT.Circular.OrientationSum
import VerticalStripLLT.Circular.ZeroAreaFibers

/-! Semantic reduction of the entire zero non-strict area family. -/

namespace VerticalStripLLT.Circular

namespace EdgeData

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem xQShift_coloringLLT_of_no_normal (G : EdgeData V E)
    (hN : G.normalEdges = ∅) (m : ℕ) :
    xQShift m (G.coloringLLT m) = G.strictOrderEnumerator ∅ m := by
  rw [G.xQShift_coloringLLT_eq_all_selected]
  simp [hN]

end EdgeData

variable {n : ℕ}

theorem shiftedOrientationExpansion_of_no_normal (D : Diagram n)
    (hN : D.edgeData.normalEdges = ∅) (θ : Orientation D) :
    shiftedOrientationExpansion D = θ.hrvMonomial := by
  classical
  have hval := Orientation.val_eq_empty_of_no_normal hN
  have huniq : ∀ ψ : Orientation D, ψ = θ := by
    intro ψ
    apply Subtype.ext
    exact (hval ψ).trans (hval θ).symm
  let : Unique (Orientation D) := ⟨⟨θ⟩, huniq⟩
  simp only [shiftedOrientationExpansion, Fintype.sum_unique, hval,
    Finset.card_empty, pow_zero, map_one, one_mul]
  exact congrArg Orientation.hrvMonomial (huniq default)

theorem coloringLLT_shifted_eq_expansion_of_no_orientation (D : Diagram n)
    (hN : D.edgeData.normalEdges = ∅) (hθ : IsEmpty (Orientation D)) (m : ℕ) :
    xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D) := by
  classical
  let : IsEmpty (Orientation D) := hθ
  have hacyclic : ¬ D.edgeData.Admissible ∅ := by
    intro h
    exact hθ.false ⟨∅, Finset.empty_subset _, h⟩
  rw [Diagram.coloringLLT, D.edgeData.xQShift_coloringLLT_of_no_normal hN,
    D.edgeData.strictOrderEnumerator_eq_zero_of_not_admissible ∅ hacyclic]
  simp [shiftedOrientationExpansion]

end VerticalStripLLT.Circular
