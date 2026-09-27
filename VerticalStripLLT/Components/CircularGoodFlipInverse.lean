import VerticalStripLLT.Components.CircularGoodFlip
import VerticalStripLLT.Components.TightFlipInverse

/-! The inverse coefficient-preserving exchange inside the original component. -/

namespace VerticalStripLLT.Circular.DirectedFlipWitness

open Classical

variable {n : ℕ} {D : Diagram n} {θ η : Orientation D}

theorem exists_coefficientInverse (w : DirectedFlipWitness D θ η)
    (β : Orientation D) (hηβ : η.val ⊆ β.val)
    (hg : D.naturalGain.ContractedGood (D.strict ∪ β.val) (D.strict ∪ η.val)) :
    ∃ α : Orientation D,
      α.val = insert w.eab (β.val.erase w.ebc) ∧
      θ.val ⊆ α.val ∧ Nonempty (DirectedFlipWitness D α β) ∧
      D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ θ.val) =
        D.naturalGain.coefficient (D.strict ∪ β.val) (D.strict ∪ η.val) := by
  obtain ⟨M, hM, z, heq, hslack⟩ :=
    D.naturalGain.exists_tightPotential_of_contractedGood
      (D.strict ∪ β.val) (D.strict ∪ η.val) (Finset.union_subset_union_right hηβ) hg
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  obtain ⟨α, hswap, hθα, hresidual, hw⟩ :=
    w.exists_tightInverse β hηβ (M : ℤ) hM' z heq hslack
  have hθ : D.naturalGain.Balanced (D.strict ∪ θ.val) := by
    apply w.balanced_iff.mpr
    obtain ⟨p, hp, _, _⟩ := hg
    exact ⟨p, hp⟩
  exact ⟨α, hswap, hθα, hw,
    w.coefficient_eq_of_residual α β hθα hηβ hθ hresidual⟩

theorem exists_coefficientInverse_in_component (w : DirectedFlipWitness D θ η)
    (γ β : Orientation D) (hβ : β ∈ flipComponent D γ)
    (hκ : D.naturalGain.coefficient (D.strict ∪ β.val) (D.strict ∪ η.val) ≠ 0) :
    ∃ α ∈ flipComponent D γ,
      α.val = insert w.eab (β.val.erase w.ebc) ∧
      Nonempty (DirectedFlipWitness D α β) ∧
      D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ θ.val) =
        D.naturalGain.coefficient (D.strict ∪ β.val) (D.strict ∪ η.val) := by
  have hg : (D.strict ∪ η.val) ⊆ (D.strict ∪ β.val) ∧
      D.naturalGain.ContractedGood (D.strict ∪ β.val) (D.strict ∪ η.val) := by
    by_contra hnot
    exact hκ (by simp [Components.GainData.coefficient, hnot])
  have hηβ : η.val ⊆ β.val := by
    intro e he
    rcases Finset.mem_union.mp (hg.1 (Finset.mem_union_right D.strict he)) with hs | ha
    · exact False.elim ((Finset.mem_sdiff.mp (η.property.1 he)).2 hs)
    · exact ha
  obtain ⟨α, hswap, _, hw, hcoeff⟩ := w.exists_coefficientInverse β hηβ hg.2
  refine ⟨α, ?_, hswap, hw, hcoeff⟩
  apply mem_flipComponent_iff.mpr
  exact (mem_flipComponent_iff.mp hβ).tail (Or.inr hw)

end VerticalStripLLT.Circular.DirectedFlipWitness
