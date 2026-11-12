import VerticalStripLLT.CyclicHessenberg.LayerList

/-! Identify the recursive list counts with the original finite positional layer definitions. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V : Type*} [LinearOrder V]

theorem spectatorCount_ofFn (a C : V) {n : ℕ} (v : Fin n → V) :
    spectatorCount a C (List.ofFn v) = ∑ i : Fin n, if a < v i ∧ v i ≤ C then 1 else 0 := by
  induction n with
  | zero => simp [spectatorCount]
  | succ n ih =>
    rw [List.ofFn_succ, spectatorCount_cons, ih, Fin.sum_univ_succ]

theorem layerListFeasible_ofFn (h : V → V) {n : ℕ} (v w : Fin n → V) :
    layerListFeasible h (List.ofFn v) (List.ofFn w) ↔ ∀ i, v i ≤ h (w i) := by
  induction n with
  | zero => simp [layerListFeasible]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, layerListFeasible, ih, Fin.forall_fin_succ]

theorem layerListAscentCount_ofFn (h : V → V) {n : ℕ} (v w : Fin n → V) :
    layerListAscentCount h (List.ofFn v) (List.ofFn w) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j ∧ v i < v j ∧ v j ≤ h (w i) then 1 else 0 := by
  induction n with
  | zero => simp [layerListAscentCount]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, layerListAscentCount, spectatorCount_ofFn, ih]
    simp [Fin.sum_univ_succ]

theorem fullOrder_ofFn {n : ℕ} (π : FullOrder n) :
    List.ofFn (fun i => (orderEquiv π i).val) = π.val :=
  congrArg Subtype.val (orderOfEquiv_orderEquiv π)

theorem layerListFeasible_eq {k : ℕ} (h : Hessenberg k) (π τ : FullOrder k) :
    layerListFeasible h π.val τ.val ↔ layerFeasible h π τ := by
  rw [← fullOrder_ofFn π, ← fullOrder_ofFn τ, layerListFeasible_ofFn]
  rfl

theorem layerListAscentCount_eq {k : ℕ} (h : Hessenberg k) (π τ : FullOrder k) :
    layerListAscentCount h π.val τ.val = layerAscentCount h π τ := by
  rw [← fullOrder_ofFn π, ← fullOrder_ofFn τ, layerListAscentCount_ofFn,
    layerAscentCount_eq_sum]

theorem layerListWeight_eq {k : ℕ} {R : Type*} [CommSemiring R]
    (h : Hessenberg k) (q : R) (π τ : FullOrder k) :
    layerListWeight h q π.val τ.val = layerKernelAt h (1 + q) π τ := by
  classical
  simp only [layerListWeight, layerKernelAt, layerListFeasible_eq, layerListAscentCount_eq]

end VerticalStripLLT.CyclicHessenberg
