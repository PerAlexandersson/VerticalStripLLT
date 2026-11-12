import VerticalStripLLT.CyclicHessenberg.ColorEvaluation
import VerticalStripLLT.CyclicHessenberg.KernelSupport

/-! A coefficient-ring-generic coloring sum, retaining its independently sorted-color semantics. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V R : Type*} [LinearOrder V] [CommRing R]

/-- Evaluate an actual list kernel on the order of a coloring, with arbitrary color weights. -/
noncomputable def weightedKernelColoring (S : Finset V)
    (Z : List V → List V → R) {m : ℕ} (weight : Fin m → R) : R :=
  ∑ κ : S → Fin m, (∏ v : S, weight (κ v)) *
    Z (sortColorOrder κ).val (sortColorOrder κ).val

theorem weightedKernelColoring_eq_classProduct (S : Finset V)
    (Z : List V → List V → R) (hZ : SupportedKernel S Z)
    {m : ℕ} (weight : Fin m → R) :
    weightedKernelColoring S Z weight =
      wordEval (fun w => Z w w) [] [] (colorClassProduct S.sort (List.ofFn weight)) := by
  exact (colorClassProduct_eval S weight (fun w => Z w w)
    (fun w hw => hZ w w (Or.inl hw))).symm

theorem weightedKernelColoring_map {T : Type*} [CommRing T] (F : R →+* T)
    (S : Finset V) (Z : List V → List V → R) {m : ℕ} (weight : Fin m → R) :
    F (weightedKernelColoring S Z weight) =
      weightedKernelColoring S (fun l t => F (Z l t)) (fun c => F (weight c)) := by
  classical
  simp only [weightedKernelColoring, map_sum, map_mul, map_prod]

/-- The generic weighted sum specializes to the pre-existing finite polynomial enumerator. -/
theorem weightedKernelColoring_eq_kernelColoringLLT (S : Finset V)
    (Z : Kernel Q S) (m : ℕ) :
    weightedKernelColoring S (fun l t => (MvPolynomial.C (kernelEntry Z l t) : XPoly m))
        MvPolynomial.X = kernelColoringLLT Z m := by
  classical
  unfold weightedKernelColoring kernelColoringLLT orderColoringEnumerator
  apply Finset.sum_congr rfl
  intro κ hκ
  simp only [kernelEntry, dite_eq_left (sortColorOrder κ).property]
  exact mul_comm _ _

theorem weightedKernelColoring_empty (Z : List V → List V → R)
    {m : ℕ} (weight : Fin m → R) : weightedKernelColoring ∅ Z weight = Z [] [] := by
  classical
  let : Unique ((∅ : Finset V) → Fin m) := {
    default := fun v => False.elim (Finset.notMem_empty v.val v.property)
    uniq := by intro κ; funext v; exact False.elim (Finset.notMem_empty v.val v.property) }
  have hsort (κ : (∅ : Finset V) → Fin m) : (sortColorOrder κ).val = [] :=
    congrArg Subtype.val (Subsingleton.elim (sortColorOrder κ) emptyOrder)
  simp [weightedKernelColoring, hsort]

end VerticalStripLLT.CyclicHessenberg
