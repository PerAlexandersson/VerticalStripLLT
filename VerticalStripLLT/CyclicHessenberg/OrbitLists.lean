import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Cycle.Factors

set_option autoImplicit false

/-! A canonical list for the cycle containing a chosen point. -/

namespace VerticalStripLLT.CyclicHessenberg

open Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Include a fixed point as a singleton in its otherwise empty permutation orbit list. -/
def correctedOrbitList (p : Equiv.Perm α) (r : α) : List α :=
  if p r = r then [r] else p.toList r

/-- The corrected orbit list is always nonempty. -/
theorem correctedOrbitList_nonempty (p : Equiv.Perm α) (r : α) :
    correctedOrbitList p r ≠ [] := by
  by_cases h : p r = r
  · simp [correctedOrbitList, h]
  · have hr : r ∈ p.support := Equiv.Perm.mem_support.mpr h
    have hpos := Equiv.Perm.length_toList_pos_of_mem_support p r hr
    simp only [correctedOrbitList, if_neg h]
    exact List.length_pos_iff.mp hpos

/-- The first entry of the corrected orbit list is the chosen point. -/
theorem correctedOrbitList_head (p : Equiv.Perm α) (r : α)
    (hn : correctedOrbitList p r ≠ []) :
    (correctedOrbitList p r).head hn = r := by
  by_cases h : p r = r
  · simp [correctedOrbitList, h]
  · have hr : r ∈ p.support := Equiv.Perm.mem_support.mpr h
    have hne : p.toList r ≠ [] := by
      intro hnil
      have hnot : r ∉ p.support := (Equiv.Perm.toList_eq_nil_iff.mp hnil)
      exact hnot hr
    have hhead := List.head_eq_getElem_zero hne
    have hfirst := Equiv.Perm.toList_getElem_zero p r hr
    have hresult : (p.toList r).head hne = r := hhead.trans hfirst
    simpa [correctedOrbitList, h] using hresult

/-- The corrected orbit list contains no repeated entries. -/
theorem correctedOrbitList_nodup (p : Equiv.Perm α) (r : α) :
    (correctedOrbitList p r).Nodup := by
  by_cases h : p r = r
  · simp [correctedOrbitList, h]
  · simp [correctedOrbitList, h, Equiv.Perm.nodup_toList]

/-- Membership in the corrected list is exactly membership in the permutation cycle. -/
theorem mem_correctedOrbitList_iff (p : Equiv.Perm α) (r x : α) :
    x ∈ correctedOrbitList p r ↔ p.SameCycle r x := by
  by_cases h : p r = r
  · constructor
    · simp only [correctedOrbitList, if_pos h, List.mem_singleton]
      intro hx
      subst x
      exact SameCycle.rfl
    · intro hcycle
      have hEq := hcycle.eq_of_left h
      subst x
      simp [correctedOrbitList, h]
  · have hr : r ∈ p.support := Equiv.Perm.mem_support.mpr h
    rw [correctedOrbitList, if_neg h, Equiv.Perm.mem_toList_iff]
    simp [hr]

/-- Any nodup list starting at `r` and acted on by `p` as its form permutation
is the corrected orbit list of `r`. -/
theorem correctedOrbitList_eq_of_action (p : Equiv.Perm α) (r : α)
    (tail : List α) (hnd : (r :: tail).Nodup)
    (hact : ∀ x ∈ r :: tail, p x = (r :: tail).formPerm x) :
    correctedOrbitList p r = r :: tail := by
  cases tail with
  | nil =>
    have hfix : p r = r := by
      simpa using hact r (by simp)
    simp [correctedOrbitList, hfix]
  | cons s tail =>
    let l := r :: s :: tail
    have hnd' : l.Nodup := hnd
    have hpr : p r = s := by
      have hh := hact r (by simp [l])
      rw [List.formPerm_apply_head r s tail hnd'] at hh
      exact hh
    have hfix : p r ≠ r := by
      intro heq
      apply (List.nodup_cons.mp hnd').1
      simp [heq.symm.trans hpr]
    have hmemForm (n : ℕ) : (l.formPerm ^ n) r ∈ l := by
      induction n with
      | zero => simp [l]
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact List.formPerm_apply_mem_of_mem ih
    have hpow (n : ℕ) : (p ^ n) r = (l.formPerm ^ n) r := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, ih]
        exact hact _ (hmemForm n)
    have hmem (x : α) : x ∈ l ↔ p.SameCycle r x := by
      constructor
      · intro hx
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        refine ⟨(i : ℤ), ?_⟩
        rw [zpow_natCast]
        calc
          (p ^ i) r = (l.formPerm ^ i) r := hpow i
          _ = l[i % l.length]'_ := List.formPerm_pow_apply_head r (s :: tail) hnd' i
          _ = l[i]'hi := by simp only [Nat.mod_eq_of_lt hi]
      · intro hcycle
        obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
        rw [← hn, hpow n]
        exact hmemForm n
    have hr : r ∈ p.support := Equiv.Perm.mem_support.mpr hfix
    have hperm : (p.toList r).Perm l := by
      apply (List.perm_ext_iff_of_nodup (Equiv.Perm.nodup_toList p r) hnd').2
      intro x
      rw [Equiv.Perm.mem_toList_iff]
      exact (and_iff_left hr).trans (hmem x).symm
    have hlen : (p.toList r).length = l.length := by
      exact hperm.length_eq
    rw [correctedOrbitList, ite_eq_right hfix]
    change p.toList r = l
    apply List.ext_getElem
    · exact hlen
    · intro i hi₁ hi₂
      rw [Equiv.Perm.getElem_toList p r i hi₁, hpow i,
        List.formPerm_pow_apply_head r (s :: tail) hnd' i]
      change l[i % l.length]'(Nat.mod_lt _ (by simp [l])) = l[i]
      simp only [Nat.mod_eq_of_lt hi₂]

end VerticalStripLLT.CyclicHessenberg
