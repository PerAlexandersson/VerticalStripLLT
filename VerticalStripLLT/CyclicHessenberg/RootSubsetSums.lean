import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

set_option autoImplicit false

/-! Reindex powerset sums according to whether they contain a distinguished root. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

/-- Sum a root-dependent term over subsets by adjoining the root to each subset. -/
theorem sum_powerset_insert_indicator {V R : Type*} [DecidableEq V]
    [AddCommMonoid R] (S : Finset V) (r : V) (hr : r ∉ S)
    (F : ∀ U : Finset V, r ∈ U → R) :
    (∑ U : (insert r S).powerset,
      if h : r ∈ U.val then F U.val h else 0) =
      ∑ U ∈ S.powerset, F (insert r U) (Finset.mem_insert_self r U) := by
  classical
  let g : Finset V → R := fun U => if h : r ∈ U then F U h else 0
  change (∑ U : (insert r S).powerset, g U.val) = _
  rw [Finset.sum_coe_sort]
  rw [Finset.sum_powerset_insert hr g]
  have hzero : (∑ U ∈ S.powerset, g U) = 0 := by
    apply Finset.sum_eq_zero
    intro U hU
    have hrU : r ∉ U := fun h => hr (Finset.mem_powerset.mp hU h)
    simp only [g, dite_eq_right hrU]
  rw [hzero, zero_add]
  apply Finset.sum_congr rfl
  intro U hU
  exact dite_eq_left (Finset.mem_insert_self r U)

/-- The same decomposition when the distinguished root already belongs to `S`. -/
theorem sum_powerset_mem_indicator {V R : Type*} [DecidableEq V]
    [AddCommMonoid R] (S : Finset V) (r : V) (hr : r ∈ S)
    (F : ∀ U : Finset V, r ∈ U → R) :
    (∑ U : S.powerset,
      if h : r ∈ U.val then F U.val h else 0) =
      ∑ U ∈ (S.erase r).powerset,
        F (insert r U) (Finset.mem_insert_self r U) := by
  simpa only [Finset.insert_erase hr] using
    sum_powerset_insert_indicator (S.erase r) r (Finset.notMem_erase r S) F

end VerticalStripLLT.CyclicHessenberg
