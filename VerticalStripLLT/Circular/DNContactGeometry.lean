import VerticalStripLLT.Circular.IndexedBounceContacts
import VerticalStripLLT.Circular.ContactEndpoints
import VerticalStripLLT.Circular.NeutralContacts

/-! Residue separation and length bounds for a complete acyclic DN contact. -/

namespace VerticalStripLLT.Circular
namespace Diagram
namespace IndexedBounceContacts

variable {n : ℕ} {D : Diagram n} {t x : ℤ} (B : D.IndexedBounceContacts t x)

include B

theorem main_injective (ha : D.edgeData.Admissible ∅) : Function.Injective B.main :=
  acyclic_walk_injective _ ha B.main B.main_steps

theorem parallel_injective (ha : D.edgeData.Admissible ∅) : Function.Injective B.parallel :=
  acyclic_walk_injective _ ha B.parallel B.parallel_steps

theorem parallel_start_free (hx : ¬ D.strictAt (x + 1)) (v : Fin n) :
    ¬ D.edgeData.selected ∅ v (B.parallel 0) := by
  rw [B.parallel_zero]
  exact D.not_selected_to_of_not_strictAt hx v

theorem parallel_end_free (ht : D.EligibleDE t) (v : Fin n) :
    ¬ D.edgeData.selected ∅ (B.parallel (Fin.last B.k)) v := by
  rw [B.parallel_last]
  exact ht.parallel_end_free D v

theorem main_parallel_disjoint (ha : D.edgeData.Admissible ∅)
    (ht : D.EligibleDE t) (hx : ¬ D.strictAt (x + 1)) :
    ∀ i j, B.main i ≠ B.parallel j :=
  parallel_paths_disjoint _ D.strict_selected_leftUnique D.strict_selected_rightUnique
    B.main B.parallel (B.main_injective ha) (B.parallel_injective ha)
    B.main_steps B.parallel_steps (B.parallel_start_free hx) (B.parallel_end_free ht)

theorem residue_ne (ha : D.edgeData.Admissible ∅) : D.residue x ≠ D.residue t := by
  intro h
  have he : B.main 1 = B.main (Fin.last (B.k + 2)) := by
    rw [B.main_one, B.main_last, h]
  have hi := congrArg Fin.val (B.main_injective ha he)
  simp only [Fin.val_one, Fin.val_last] at hi
  lia

theorem next_residue_ne (ha : D.edgeData.Admissible ∅)
    (ht : D.EligibleDE t) (hx : ¬ D.strictAt (x + 1)) :
    D.residue (x + 1) ≠ D.residue t := by
  have h := B.main_parallel_disjoint ha ht hx (Fin.last (B.k + 2)) 0
  rw [B.main_last, B.parallel_zero] at h
  exact h.symm

theorem first_area_bound (ha : D.edgeData.Admissible ∅)
    (ht : D.EligibleDE t) (hx : ¬ D.strictAt (x + 1)) :
    D.area.area (D.residue x) + 1 < n := by
  have hne := B.main_parallel_disjoint ha ht hx 0 0
  rw [B.main_zero, B.parallel_zero] at hne
  have hb := D.area.bound (D.residue x)
  by_contra h
  have heq : D.area.area (D.residue x) + 1 = n := by lia
  have heq' : (D.area.area (D.residue x) : ℤ) + 1 = n := by exact_mod_cast heq
  have hboundary : D.boundary x = x + 1 + (n : ℤ) * (-1) := by
    unfold boundary
    lia
  apply hne
  rw [hboundary, D.residue_add_period]

end IndexedBounceContacts
end Diagram
end VerticalStripLLT.Circular
