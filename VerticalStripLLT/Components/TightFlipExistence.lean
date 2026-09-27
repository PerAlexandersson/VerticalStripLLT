import VerticalStripLLT.Components.TightFlipReconstruction

/-!
# Extending a tight circular flip to its ambient selection

A scaled potential tight on the source subgraph and strictly slack elsewhere
forces the missing short edge to stay absent. Exchanging the shorts gives an
admissible ambient orientation and an actual flip with every integer-cover test.
-/

namespace VerticalStripLLT.Circular.DirectedFlipWitness

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n} {θ η : Orientation D}

/-- The retained long edge and source short force the target short to be tight. -/
theorem bc_eq_of_tightSelection (w : DirectedFlipWitness D θ η)
    (M : ℤ) (z : Fin n → ℤ)
    (heqθ : ∀ e ∈ D.strict ∪ θ.val,
      z e.head - z e.tail = M * (e.length.val : ℤ)) :
    z w.ebc.head - z w.ebc.tail = M * (w.ebc.length.val : ℤ) := by
  have hab := heqθ w.eab (Finset.mem_union_right _ w.source_ab_mem)
  have hac := heqθ w.longEdge w.longEdge_mem
  rw [w.short_head_tail] at hab
  rw [← w.longEdge_head, ← w.longEdge_tail, w.longEdge_length, mul_add] at hac
  lia

/-- A forced-tight short cannot occur among the ambient strictly slack edges. -/
theorem bc_not_mem_of_tightSelection (w : DirectedFlipWitness D θ η)
    (α : Orientation D) (M : ℤ) (z : Fin n → ℤ)
    (heqθ : ∀ e ∈ D.strict ∪ θ.val,
      z e.head - z e.tail = M * (e.length.val : ℤ))
    (hslack : ∀ e ∈ (D.strict ∪ α.val) \ (D.strict ∪ θ.val),
      M * (e.length.val : ℤ) < z e.head - z e.tail) :
    w.ebc ∉ α.val := by
  intro hbc
  have hnot : w.ebc ∉ D.strict ∪ θ.val := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact (Finset.mem_sdiff.mp w.ebc_normal).2 h
    · exact w.source_bc_not_mem h
  have hs := hslack w.ebc
    (Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hbc, hnot⟩)
  have he := w.bc_eq_of_tightSelection M z heqθ
  lia

/-- Construct the ambient exchange, preserving residual edges and the actual flip relation. -/
theorem exists_tightExtension (w : DirectedFlipWitness D θ η)
    (α : Orientation D) (hθα : θ.val ⊆ α.val) (M : ℤ) (hM : 0 < M)
    (z : Fin n → ℤ)
    (heqθ : ∀ e ∈ D.strict ∪ θ.val,
      z e.head - z e.tail = M * (e.length.val : ℤ))
    (hslack : ∀ e ∈ (D.strict ∪ α.val) \ (D.strict ∪ θ.val),
      M * (e.length.val : ℤ) < z e.head - z e.tail) :
    ∃ β : Orientation D,
      β.val = insert w.ebc (α.val.erase w.eab) ∧
      η.val ⊆ β.val ∧
      (D.strict ∪ β.val) \ (D.strict ∪ η.val) =
        (D.strict ∪ α.val) \ (D.strict ∪ θ.val) ∧
      Nonempty (DirectedFlipWitness D α β) := by
  have hbc := w.bc_not_mem_of_tightSelection α M z heqθ hslack
  have hbcEq := w.bc_eq_of_tightSelection M z heqθ
  let B : Finset (Edge D.area) := insert w.ebc (α.val.erase w.eab)
  have hnormal : B ⊆ D.edgeData.normalEdges := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact w.ebc_normal
    · exact α.property.1 (Finset.mem_erase.mp he).2
  have hηB : η.val ⊆ B := by
    intro e he
    rw [w.target_eq_source_swap] at he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp he).1, hθα (Finset.mem_erase.mp he).2⟩)
  have hresidual : (D.strict ∪ B) \ (D.strict ∪ η.val) =
      (D.strict ∪ α.val) \ (D.strict ∪ θ.val) := by
    rw [w.target_eq_source_swap]
    ext e
    have hab := w.source_ab_mem
    simp only [B, Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert,
      Finset.mem_erase]
    grind
  have hweakα : ∀ e ∈ D.strict ∪ α.val,
      M * (e.length.val : ℤ) ≤ z e.head - z e.tail := by
    intro e he
    by_cases ht : e ∈ D.strict ∪ θ.val
    · exact (heqθ e ht).ge
    · exact le_of_lt (hslack e (Finset.mem_sdiff.mpr ⟨he, ht⟩))
  have hweakB : ∀ e ∈ D.strict ∪ B,
      M * (e.length.val : ℤ) ≤ z e.head - z e.tail := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hweakα e (Finset.mem_union_left _ he)
    · rcases Finset.mem_insert.mp he with rfl | he
      · exact hbcEq.ge
      · exact hweakα e (Finset.mem_union_right _ (Finset.mem_erase.mp he).2)
  let β : Orientation D := ⟨B, hnormal, D.admissible_of_scaled_potential hM hweakB⟩
  have htightα : ∀ e ∈ D.strict ∪ α.val,
      z e.head - z e.tail = M * (e.length.val : ℤ) → e ∈ D.strict ∪ θ.val := by
    intro e he heq
    by_contra hnot
    have hs := hslack e (Finset.mem_sdiff.mpr ⟨he, hnot⟩)
    lia
  have htightβ : ∀ e ∈ D.strict ∪ β.val,
      z e.head - z e.tail = M * (e.length.val : ℤ) → e ∈ D.strict ∪ η.val := by
    intro e he heq
    by_contra hnot
    have hmem : e ∈ (D.strict ∪ B) \ (D.strict ∪ η.val) :=
      Finset.mem_sdiff.mpr ⟨he, hnot⟩
    rw [hresidual] at hmem
    have hs := hslack e hmem
    lia
  exact ⟨β, rfl, hηB, hresidual,
    ⟨w.of_tightSelections α β hθα hηB rfl M z hweakα hweakB htightα htightβ heqθ⟩⟩

end

end VerticalStripLLT.Circular.DirectedFlipWitness
