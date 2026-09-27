import VerticalStripLLT.Components.TightFlipReconstruction
import VerticalStripLLT.Components.EdgeSwap

/-!
# Reconstructing the source of an ambient tight flip

Starting from an ambient extension of the target, exchange the short edges back.
The reconstructed witness still has the original direction from source to target.
-/

namespace VerticalStripLLT.Circular.DirectedFlipWitness

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n} {θ η : Orientation D}

/-- Target tightness on the long edge and its short forces source-short tightness. -/
theorem ab_eq_of_tightTarget (w : DirectedFlipWitness D θ η)
    (M : ℤ) (z : Fin n → ℤ)
    (heqη : ∀ e ∈ D.strict ∪ η.val,
      z e.head - z e.tail = M * (e.length.val : ℤ)) :
    z w.eab.head - z w.eab.tail = M * (w.eab.length.val : ℤ) := by
  have hbc := heqη w.ebc (Finset.mem_union_right _ w.target_bc_mem)
  have hac := heqη w.longEdge w.longEdge_target_mem
  rw [← w.longEdge_head, ← w.longEdge_tail, w.longEdge_length, mul_add] at hac
  rw [w.short_head_tail]
  lia

/-- The absent source short cannot be a strictly slack edge of a target extension. -/
theorem ab_not_mem_of_tightTarget (w : DirectedFlipWitness D θ η)
    (β : Orientation D) (M : ℤ) (z : Fin n → ℤ)
    (heqη : ∀ e ∈ D.strict ∪ η.val,
      z e.head - z e.tail = M * (e.length.val : ℤ))
    (hslack : ∀ e ∈ (D.strict ∪ β.val) \ (D.strict ∪ η.val),
      M * (e.length.val : ℤ) < z e.head - z e.tail) :
    w.eab ∉ β.val := by
  intro hab
  have hnot : w.eab ∉ D.strict ∪ η.val := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact (Finset.mem_sdiff.mp w.eab_normal).2 h
    · exact w.target_ab_not_mem h
  have hs := hslack w.eab
    (Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hab, hnot⟩)
  have he := w.ab_eq_of_tightTarget M z heqη
  lia

/-- Invert the ambient short exchange, preserving residual edges and flip direction. -/
theorem exists_tightInverse (w : DirectedFlipWitness D θ η)
    (β : Orientation D) (hηβ : η.val ⊆ β.val) (M : ℤ) (hM : 0 < M)
    (z : Fin n → ℤ)
    (heqη : ∀ e ∈ D.strict ∪ η.val,
      z e.head - z e.tail = M * (e.length.val : ℤ))
    (hslack : ∀ e ∈ (D.strict ∪ β.val) \ (D.strict ∪ η.val),
      M * (e.length.val : ℤ) < z e.head - z e.tail) :
    ∃ α : Orientation D,
      α.val = insert w.eab (β.val.erase w.ebc) ∧
      θ.val ⊆ α.val ∧
      (D.strict ∪ α.val) \ (D.strict ∪ θ.val) =
        (D.strict ∪ β.val) \ (D.strict ∪ η.val) ∧
      Nonempty (DirectedFlipWitness D α β) := by
  have hab := w.ab_not_mem_of_tightTarget β M z heqη hslack
  have habEq := w.ab_eq_of_tightTarget M z heqη
  have hθswap : θ.val = insert w.eab (η.val.erase w.ebc) := by
    have h := Components.insert_erase_exchange_inverse θ.val
      w.source_ab_mem w.source_bc_not_mem
    rw [← w.target_eq_source_swap] at h
    exact h.symm
  let A : Finset (Edge D.area) := insert w.eab (β.val.erase w.ebc)
  have hnormal : A ⊆ D.edgeData.normalEdges := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact w.eab_normal
    · exact β.property.1 (Finset.mem_erase.mp he).2
  have hθA : θ.val ⊆ A := by
    intro e he
    rw [hθswap] at he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp he).1, hηβ (Finset.mem_erase.mp he).2⟩)
  have hswap : β.val = insert w.ebc (A.erase w.eab) := by
    exact (Components.insert_erase_exchange_inverse β.val
      (hηβ w.target_bc_mem) hab).symm
  have hresidual : (D.strict ∪ A) \ (D.strict ∪ θ.val) =
      (D.strict ∪ β.val) \ (D.strict ∪ η.val) := by
    rw [hθswap]
    ext e
    have hbc := w.target_bc_mem
    simp only [A, Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert,
      Finset.mem_erase]
    grind
  have hweakβ : ∀ e ∈ D.strict ∪ β.val,
      M * (e.length.val : ℤ) ≤ z e.head - z e.tail := by
    intro e he
    by_cases ht : e ∈ D.strict ∪ η.val
    · exact (heqη e ht).ge
    · exact le_of_lt (hslack e (Finset.mem_sdiff.mpr ⟨he, ht⟩))
  have hweakA : ∀ e ∈ D.strict ∪ A,
      M * (e.length.val : ℤ) ≤ z e.head - z e.tail := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hweakβ e (Finset.mem_union_left _ he)
    · rcases Finset.mem_insert.mp he with rfl | he
      · exact habEq.ge
      · exact hweakβ e (Finset.mem_union_right _ (Finset.mem_erase.mp he).2)
  let α : Orientation D := ⟨A, hnormal, D.admissible_of_scaled_potential hM hweakA⟩
  have htightβ : ∀ e ∈ D.strict ∪ β.val,
      z e.head - z e.tail = M * (e.length.val : ℤ) → e ∈ D.strict ∪ η.val := by
    intro e he heq
    by_contra hnot
    have hs := hslack e (Finset.mem_sdiff.mpr ⟨he, hnot⟩)
    lia
  have htightα : ∀ e ∈ D.strict ∪ α.val,
      z e.head - z e.tail = M * (e.length.val : ℤ) → e ∈ D.strict ∪ θ.val := by
    intro e he heq
    by_contra hnot
    have hmem : e ∈ (D.strict ∪ A) \ (D.strict ∪ θ.val) :=
      Finset.mem_sdiff.mpr ⟨he, hnot⟩
    rw [hresidual] at hmem
    have hs := hslack e hmem
    lia
  have heqθ : ∀ e ∈ D.strict ∪ θ.val,
      z e.head - z e.tail = M * (e.length.val : ℤ) := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact heqη e (Finset.mem_union_left _ he)
    · rw [hθswap] at he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact habEq
      · exact heqη e (Finset.mem_union_right _ (Finset.mem_erase.mp he).2)
  exact ⟨α, rfl, hθA, hresidual,
    ⟨w.of_tightSelections α β hθA hηβ hswap M z hweakA hweakβ htightα htightβ heqθ⟩⟩

end

end VerticalStripLLT.Circular.DirectedFlipWitness
