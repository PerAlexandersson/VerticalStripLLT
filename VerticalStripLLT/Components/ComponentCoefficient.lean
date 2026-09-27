import VerticalStripLLT.Components.CircularGoodFlipInverse

/-! Constancy of companion coefficient sums along complete circular flip components. -/

namespace VerticalStripLLT.Circular

open Classical
open scoped BigOperators

variable {n : ℕ} {D : Diagram n}

/-- Sum the canonical companion coefficient over the original complete component. -/
noncomputable def componentCoefficient (D : Diagram n) (γ θ : Orientation D) : ℤ :=
  ∑ α ∈ flipComponent D γ,
    D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ θ.val)

private theorem nonzero_coefficient_data (θ α : Orientation D)
    (hκ : D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ θ.val) ≠ 0) :
    θ.val ⊆ α.val ∧
      D.naturalGain.ContractedGood (D.strict ∪ α.val) (D.strict ∪ θ.val) := by
  have hg : (D.strict ∪ θ.val) ⊆ (D.strict ∪ α.val) ∧
      D.naturalGain.ContractedGood (D.strict ∪ α.val) (D.strict ∪ θ.val) := by
    by_contra hnot
    exact hκ (by simp [Components.GainData.coefficient, hnot])
  refine ⟨?_, hg.2⟩
  intro e he
  rcases Finset.mem_union.mp (hg.1 (Finset.mem_union_right D.strict he)) with hs | ha
  · exact False.elim ((Finset.mem_sdiff.mp (θ.property.1 he)).2 hs)
  · exact ha

namespace DirectedFlipWitness

variable {θ η : Orientation D}

private theorem source_short_membership (w : DirectedFlipWitness D θ η)
    (α : Orientation D)
    (hκ : D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ θ.val) ≠ 0) :
    w.eab ∈ α.val ∧ w.ebc ∉ α.val := by
  obtain ⟨hθα, hg⟩ := nonzero_coefficient_data θ α hκ
  obtain ⟨M, _, z, heq, hslack⟩ :=
    D.naturalGain.exists_tightPotential_of_contractedGood
      (D.strict ∪ α.val) (D.strict ∪ θ.val) (Finset.union_subset_union_right hθα) hg
  exact ⟨hθα w.source_ab_mem, w.bc_not_mem_of_tightSelection α M z heq hslack⟩

/-- The finite weighted exchange stays in the original component on both sides. -/
theorem componentCoefficient_eq (w : DirectedFlipWitness D θ η) (γ : Orientation D) :
    componentCoefficient D γ θ = componentCoefficient D γ η := by
  let kθ := fun α : Orientation D =>
    D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ θ.val)
  let kη := fun α : Orientation D =>
    D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ η.val)
  let s := (flipComponent D γ).filter fun α => kθ α ≠ 0
  let t := (flipComponent D γ).filter fun β => kη β ≠ 0
  have hf : ∀ α, α ∈ s → ∃ β ∈ t,
      β.val = insert w.ebc (α.val.erase w.eab) ∧ kθ α = kη β := by
    intro α hα
    obtain ⟨hαC, hακ⟩ := Finset.mem_filter.mp hα
    obtain ⟨β, hβ, hswap, _, heq⟩ :=
      w.exists_coefficientExtension_in_component γ α hαC hακ
    change kθ α = kη β at heq
    exact ⟨β, Finset.mem_filter.mpr ⟨hβ, by rwa [← heq]⟩, hswap, heq⟩
  choose f hfm hfs hfk using hf
  have hsum : (∑ α ∈ s, kθ α) = ∑ β ∈ t, kη β := by
    apply Finset.sum_bij f hfm
    · intro α hα α' hα' heq
      have hαshort := w.source_short_membership α (Finset.mem_filter.mp hα).2
      have hα'short := w.source_short_membership α' (Finset.mem_filter.mp hα').2
      have hv : insert w.ebc (α.val.erase w.eab) =
          insert w.ebc (α'.val.erase w.eab) := by
        rw [← hfs α hα, ← hfs α' hα', heq]
      have hinv := congrArg (fun X => insert w.eab (X.erase w.ebc)) hv
      rw [Components.insert_erase_exchange_inverse _ hαshort.1 hαshort.2,
        Components.insert_erase_exchange_inverse _ hα'short.1 hα'short.2] at hinv
      exact Subtype.ext hinv
    · intro β hβ
      obtain ⟨hβC, hβκ⟩ := Finset.mem_filter.mp hβ
      obtain ⟨α, hαC, hαval, _, hk⟩ :=
        w.exists_coefficientInverse_in_component γ β hβC hβκ
      change kθ α = kη β at hk
      have hα : α ∈ s := Finset.mem_filter.mpr ⟨hαC, by rwa [hk]⟩
      refine ⟨α, hα, ?_⟩
      apply Subtype.ext
      rw [hfs α hα, hαval]
      obtain ⟨hηβ, hg⟩ := nonzero_coefficient_data η β hβκ
      obtain ⟨M, _, z, heq, hslack⟩ :=
        D.naturalGain.exists_tightPotential_of_contractedGood
          (D.strict ∪ β.val) (D.strict ∪ η.val)
          (Finset.union_subset_union_right hηβ) hg
      exact Components.insert_erase_exchange_inverse β.val (hηβ w.target_bc_mem)
        (w.ab_not_mem_of_tightTarget β M z heq hslack)
    · exact hfk
  simpa only [s, t, Finset.sum_filter_ne_zero, componentCoefficient, kθ, kη] using hsum

end DirectedFlipWitness

theorem componentCoefficient_eq_of_flip (γ : Orientation D) {θ η : Orientation D}
    (h : Flip D θ η) : componentCoefficient D γ θ = componentCoefficient D γ η := by
  rcases h with h | h
  · exact h.some.componentCoefficient_eq γ
  · exact (h.some.componentCoefficient_eq γ).symm

theorem componentCoefficient_eq_of_reachable (γ : Orientation D) {θ η : Orientation D}
    (h : Relation.ReflTransGen (Flip D) θ η) :
    componentCoefficient D γ θ = componentCoefficient D γ η := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (componentCoefficient_eq_of_flip γ hs)

theorem componentCoefficient_eq_of_mem_flipComponent (γ : Orientation D)
    {θ η : Orientation D} (h : η ∈ flipComponent D θ) :
    componentCoefficient D γ θ = componentCoefficient D γ η :=
  componentCoefficient_eq_of_reachable γ (mem_flipComponent_iff.mp h)

end VerticalStripLLT.Circular
