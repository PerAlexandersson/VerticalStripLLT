import VerticalStripLLT.Components.FlipTriangle
import VerticalStripLLT.Components.GainTriangleSwap
import VerticalStripLLT.Components.CircularGainData
import VerticalStripLLT.Components.GainCoefficientTransport

/-! Balanced selected graphs and their coefficients under actual circular flips. -/

namespace VerticalStripLLT.Circular

open Classical

variable {n : ℕ} {D : Diagram n}

namespace DirectedFlipWitness

variable {θ η : Orientation D}

theorem balancedPotential_iff (w : DirectedFlipWitness D θ η) (p : Fin n → ℤ) :
    D.naturalGain.BalancedPotential (D.strict ∪ θ.val) p ↔
      D.naturalGain.BalancedPotential (D.strict ∪ η.val) p := by
  rw [w.full_target_eq_source_swap]
  exact D.naturalGain.balancedPotential_triangle_swap
    (Finset.mem_union_right _ w.source_ab_mem) w.longEdge_mem
    (Ne.symm w.longEdge_ne_ab) w.longEdge_tail w.short_head_tail w.longEdge_head
    w.longEdge_length

theorem weakClosure_iff (w : DirectedFlipWitness D θ η) (u v : Fin n) :
    Relation.EqvGen (D.naturalGain.selectedRelation (D.strict ∪ θ.val)) u v ↔
      Relation.EqvGen (D.naturalGain.selectedRelation (D.strict ∪ η.val)) u v := by
  rw [w.full_target_eq_source_swap]
  exact D.naturalGain.selectedRelation_eqvGen_triangle_swap
    (Finset.mem_union_right _ w.source_ab_mem) w.longEdge_mem
    (Ne.symm w.longEdge_ne_ab) w.longEdge_tail w.short_head_tail w.longEdge_head

theorem balanced_iff (w : DirectedFlipWitness D θ η) :
    D.naturalGain.Balanced (D.strict ∪ θ.val) ↔
      D.naturalGain.Balanced (D.strict ∪ η.val) := by
  exact exists_congr (fun p => w.balancedPotential_iff p)

/-- The same balanced potential and residual edges give the same actual coefficient. -/
theorem coefficient_eq_of_residual (w : DirectedFlipWitness D θ η)
    (α β : Orientation D) (hθα : θ.val ⊆ α.val) (hηβ : η.val ⊆ β.val)
    (hθ : D.naturalGain.Balanced (D.strict ∪ θ.val))
    (hresidual : (D.strict ∪ α.val) \ (D.strict ∪ θ.val) =
      (D.strict ∪ β.val) \ (D.strict ∪ η.val)) :
    D.naturalGain.coefficient (D.strict ∪ α.val) (D.strict ∪ θ.val) =
      D.naturalGain.coefficient (D.strict ∪ β.val) (D.strict ∪ η.val) := by
  obtain ⟨p, hp⟩ := hθ
  exact D.naturalGain.coefficient_eq_of_common_potential
    (Finset.union_subset_union_right hθα) (Finset.union_subset_union_right hηβ)
    hp ((w.balancedPotential_iff p).mp hp) w.weakClosure_iff hresidual

end DirectedFlipWitness

theorem balanced_iff_of_flip {θ η : Orientation D} (h : Flip D θ η) :
    D.naturalGain.Balanced (D.strict ∪ θ.val) ↔
      D.naturalGain.Balanced (D.strict ∪ η.val) := by
  rcases h with h | h
  · exact h.some.balanced_iff
  · exact h.some.balanced_iff.symm

theorem balanced_iff_of_flip_reachable {θ η : Orientation D}
    (h : Relation.ReflTransGen (Flip D) θ η) :
    D.naturalGain.Balanced (D.strict ∪ θ.val) ↔
      D.naturalGain.Balanced (D.strict ∪ η.val) := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (balanced_iff_of_flip hs)

theorem balanced_iff_of_mem_flipComponent {θ η : Orientation D}
    (h : η ∈ flipComponent D θ) :
    D.naturalGain.Balanced (D.strict ∪ θ.val) ↔
      D.naturalGain.Balanced (D.strict ∪ η.val) :=
  balanced_iff_of_flip_reachable (mem_flipComponent_iff.mp h)

end VerticalStripLLT.Circular
