import VerticalStripLLT.Components.TightFlipExistence
import VerticalStripLLT.Components.CircularBalancedFlip
import VerticalStripLLT.Components.GainTightPotential

/-! Coefficient-preserving extensions of balanced flips inside the original component. -/

namespace VerticalStripLLT.Circular.DirectedFlipWitness

open Classical

variable {n : ℕ} {D : Diagram n} {θ η : Orientation D}

theorem exists_coefficientExtension (w : DirectedFlipWitness D θ η)
    (α : Orientation D) (hθα : θ.val ⊆ α.val)
    (hg : D.naturalGain.ContractedGood (D.strict ∪ α.val) (D.strict ∪ θ.val)) :
    ∃ β : Orientation D,
      β.val = insert w.ebc (α.val.erase w.eab) ∧
      η.val ⊆ β.val ∧ Nonempty (DirectedFlipWitness D α β) ∧
      D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ θ.val) =
        D.naturalGain.coefficient (D.strict ∪ β.val) (D.strict ∪ η.val) := by
  obtain ⟨M, hM, z, heq, hslack⟩ :=
    D.naturalGain.exists_tightPotential_of_contractedGood
      (D.strict ∪ α.val) (D.strict ∪ θ.val) (Finset.union_subset_union_right hθα) hg
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  obtain ⟨β, hswap, hηβ, hresidual, hw⟩ :=
    w.exists_tightExtension α hθα (M : ℤ) hM' z heq hslack
  have hθ : D.naturalGain.Balanced (D.strict ∪ θ.val) := by
    obtain ⟨p, hp, _, _⟩ := hg
    exact ⟨p, hp⟩
  exact ⟨β, hswap, hηβ, hw,
    w.coefficient_eq_of_residual α β hθα hηβ hθ hresidual.symm⟩

/-- Nonzero companion terms exchange within the same original complete component. -/
theorem exists_coefficientExtension_in_component (w : DirectedFlipWitness D θ η)
    (γ α : Orientation D) (hα : α ∈ flipComponent D γ)
    (hκ : D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ θ.val) ≠ 0) :
    ∃ β ∈ flipComponent D γ,
      β.val = insert w.ebc (α.val.erase w.eab) ∧
      Nonempty (DirectedFlipWitness D α β) ∧
      D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ θ.val) =
        D.naturalGain.coefficient (D.strict ∪ β.val) (D.strict ∪ η.val) := by
  have hg : (D.strict ∪ θ.val) ⊆ (D.strict ∪ α.val) ∧
      D.naturalGain.ContractedGood (D.strict ∪ α.val) (D.strict ∪ θ.val) := by
    by_contra hnot
    exact hκ (by simp [Components.GainData.coefficient, hnot])
  have hθα : θ.val ⊆ α.val := by
    intro e he
    rcases Finset.mem_union.mp (hg.1 (Finset.mem_union_right D.strict he)) with hs | ha
    · exact False.elim ((Finset.mem_sdiff.mp (θ.property.1 he)).2 hs)
    · exact ha
  obtain ⟨β, hswap, _, hw, hcoeff⟩ := w.exists_coefficientExtension α hθα hg.2
  refine ⟨β, ?_, hswap, hw, hcoeff⟩
  apply mem_flipComponent_iff.mpr
  exact (mem_flipComponent_iff.mp hα).tail (Or.inl hw)

end VerticalStripLLT.Circular.DirectedFlipWitness
