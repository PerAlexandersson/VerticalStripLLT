import VerticalStripLLT.Components.UndecoratedSelection
import VerticalStripLLT.Components.FlipTriangle
import VerticalStripLLT.Components.ShortEdges

/-!
# Flips after forgetting strict markings

The lifted relation is unchanged by moving strict edges into the selection.
Conversely, a flip in the same-area undecorated diagram cannot exchange an
originally strict edge: both exchanged shorts are proper parts of a natural
long interval. This is the local argument of the universal-ambient lemma.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Circular

open Classical

variable {n : ℕ} {D : Diagram n}

namespace Orientation

/-- Forgetting strict markings preserves the entire integer cover relation. -/
theorem toUndecorated_liftCover (θ : Orientation D) :
    D.undecorated.liftCover θ.toUndecorated.val = D.liftCover θ.val := by
  funext x y
  unfold Diagram.liftCover
  rw [θ.toUndecorated_liftStep]

end Orientation

namespace DirectedFlipWitness

variable {θ η : Orientation D}

/-- Every original directed flip is the same directed flip after undecoration. -/
def toUndecorated (w : DirectedFlipWitness D θ η) :
    DirectedFlipWitness D.undecorated θ.toUndecorated η.toUndecorated where
  a := w.a
  b := w.b
  c := w.c
  cyclicWindow := w.cyclicWindow
  eab := w.eab
  ebc := w.ebc
  eab_normal := by
    rw [D.undecorated_normalEdges]
    exact Finset.mem_univ _
  ebc_normal := by
    rw [D.undecorated_normalEdges]
    exact Finset.mem_univ _
  ab_lift := w.ab_lift
  bc_lift := w.bc_lift
  source_ab := by rw [θ.toUndecorated_liftCover]; exact w.source_ab
  source_ac := by rw [θ.toUndecorated_liftCover]; exact w.source_ac
  source_not_bc := by rw [θ.toUndecorated_liftCover]; exact w.source_not_bc
  target_ac := by rw [η.toUndecorated_liftCover]; exact w.target_ac
  target_bc := by rw [η.toUndecorated_liftCover]; exact w.target_bc
  target_not_ab := by rw [η.toUndecorated_liftCover]; exact w.target_not_ab
  agree_elsewhere := by
    intro e hab hbc
    change e ∈ D.strict ∪ θ.val ↔ e ∈ D.strict ∪ η.val
    simp only [Finset.mem_union, w.agree_elsewhere e hab hbc]

variable {α β : Orientation D.undecorated}

/-- Even in the undecorated graph, both shorts are normal in the original diagram. -/
theorem undecorated_shorts_normal (w : DirectedFlipWitness D.undecorated α β) :
    w.eab ∈ D.edgeData.normalEdges ∧ w.ebc ∈ D.edgeData.normalEdges := by
  have hlong : D.naturalLift w.longEdge w.a w.c := w.longEdge_lift
  obtain ⟨eab, ebc, hab, hbc, habLift, hbcLift⟩ :=
    D.normalShortEdges_of_naturalLift hlong w.cyclicWindow.1 w.cyclicWindow.2.1
  have heab : eab = w.eab := D.naturalLift_injective habLift w.ab_lift
  have hebc : ebc = w.ebc := D.naturalLift_injective hbcLift w.bc_lift
  exact ⟨heab ▸ hab, hebc ▸ hbc⟩

/-- Every originally strict edge has unchanged membership across an undecorated flip. -/
theorem undecorated_strict_mem_iff (w : DirectedFlipWitness D.undecorated α β)
    {e : Edge D.area} (he : e ∈ D.strict) : e ∈ α.val ↔ e ∈ β.val := by
  obtain ⟨hab, hbc⟩ := w.undecorated_shorts_normal (D := D)
  have hneab : e ≠ w.eab := by
    intro h
    exact (Finset.mem_sdiff.mp hab).2 (h ▸ he)
  have hnebc : e ≠ w.ebc := by
    intro h
    exact (Finset.mem_sdiff.mp hbc).2 (h ▸ he)
  exact w.agree_elsewhere e hneab hnebc

end DirectedFlipWitness

/-- Adjacency in an original diagram is preserved after forgetting strict markings. -/
theorem flip_toUndecorated {θ η : Orientation D} (h : Flip D θ η) :
    Flip D.undecorated θ.toUndecorated η.toUndecorated := by
  rcases h with h | h
  · exact Or.inl ⟨h.some.toUndecorated⟩
  · exact Or.inr ⟨h.some.toUndecorated⟩

theorem strict_mem_iff_of_undecorated_flip {α β : Orientation D.undecorated}
    (h : Flip D.undecorated α β) {e : Edge D.area} (he : e ∈ D.strict) :
    e ∈ α.val ↔ e ∈ β.val := by
  rcases h with h | h
  · exact h.some.undecorated_strict_mem_iff (D := D) he
  · exact (h.some.undecorated_strict_mem_iff (D := D) he).symm

/-- A flip in the undecorated graph preserves containing all original strict edges. -/
theorem strict_subset_iff_of_undecorated_flip {α β : Orientation D.undecorated}
    (h : Flip D.undecorated α β) : D.strict ⊆ α.val ↔ D.strict ⊆ β.val := by
  constructor
  · intro hs e he
    exact (strict_mem_iff_of_undecorated_flip (D := D) h he).mp (hs he)
  · intro hs e he
    exact (strict_mem_iff_of_undecorated_flip (D := D) h he).mpr (hs he)

/-- The strict-containment condition is constant on entire undecorated components. -/
theorem strict_subset_iff_of_undecorated_reachable {α β : Orientation D.undecorated}
    (h : Relation.ReflTransGen (Flip D.undecorated) α β) :
    D.strict ⊆ α.val ↔ D.strict ⊆ β.val := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hs ih => exact ih.trans (strict_subset_iff_of_undecorated_flip (D := D) hs)

end VerticalStripLLT.Circular
