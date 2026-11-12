import VerticalStripLLT.CyclicHessenberg.OrbitLists

set_option autoImplicit false

/-! The form permutation of a corrected orbit list acts as the original permutation. -/

namespace VerticalStripLLT.CyclicHessenberg

open Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- On each member of its corrected orbit list, the list form permutation acts as `p`. -/
theorem correctedOrbitList_formPerm_apply (p : Equiv.Perm α) (r x : α)
    (hx : x ∈ correctedOrbitList p r) :
    (correctedOrbitList p r).formPerm x = p x := by
  by_cases hfix : p r = r
  · have hx' : x = r := by
      simpa [correctedOrbitList, hfix] using hx
    subst x
    simp [correctedOrbitList, hfix]
  · have hx' : x ∈ p.toList r := by
      simpa [correctedOrbitList, hfix] using hx
    simp only [correctedOrbitList, ite_eq_right hfix]
    rw [List.formPerm_apply_mem_eq_next (Equiv.Perm.nodup_toList p r) x hx',
      Equiv.Perm.next_toList_eq_apply p r x hx']

/-- The form permutation agrees with `p` on every member of the corrected orbit list. -/
theorem correctedOrbitList_formPerm_action (p : Equiv.Perm α) (r : α) :
    ∀ x ∈ correctedOrbitList p r,
      (correctedOrbitList p r).formPerm x = p x := by
  intro x hx
  exact correctedOrbitList_formPerm_apply p r x hx

/-- Transfer the action statement to an explicit cons representation. -/
theorem correctedOrbitList_eq_cons_formPerm_action (p : Equiv.Perm α) (r : α)
    (tail : List α) (h : correctedOrbitList p r = r :: tail) :
    ∀ x ∈ r :: tail, (r :: tail).formPerm x = p x := by
  intro x hx
  rw [← h] at hx ⊢
  exact correctedOrbitList_formPerm_apply p r x hx

end VerticalStripLLT.CyclicHessenberg
