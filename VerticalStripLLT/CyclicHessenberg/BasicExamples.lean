import VerticalStripLLT.CyclicHessenberg.RecursivePositivity

/-! Small explicit boundary cases for the source and its recursive expansion. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

@[simp] theorem loopColoringLLT_empty_support {n m : ℕ} (h : Tuple 0 n) :
    loopColoringLLT h m = 1 :=
  loopColoringLLT_empty h m

@[simp] theorem naturalRecursiveCyclicExpansion_empty_support {n : ℕ}
    (h : Tuple 0 n) :
    naturalRecursiveCyclicExpansion h =
      MvPolynomial.C (kernelEntry (naturalOpenKernel h) [] []) := by
  simp [naturalRecursiveCyclicExpansion, naturalKernelExpansion_empty]

@[simp] theorem recursiveCyclicExpansion_empty_support {n : ℕ} (h : Tuple 0 n) :
    recursiveCyclicExpansion h =
      MvPolynomial.C
        (naturalPolynomialCast (kernelEntry (naturalOpenKernel h) [] [])) := by
  simp [recursiveCyclicExpansion, naturalRecursiveCyclicExpansion,
    naturalKernelExpansion_empty, naturalCast, naturalPolynomialCast]

@[simp] theorem loopColoringLLT_zero_alphabet_explicit {k n : ℕ}
    (h : Tuple k n) (hk : 0 < k) :
    loopColoringLLT h 0 = 0 :=
  loopColoringLLT_zero_alphabet h hk

private theorem loopAscentEvents_singleton {n : ℕ} (h : Tuple 1 n)
    (L : LoopCover h) : loopAscentEvents h L = ∅ := by
  classical
  ext e
  have hab : e.2.1 = e.2.2 := Subsingleton.elim _ _
  simp [loopAscentEvents, hab]

theorem loopColoringLLT_singleton {n m : ℕ} (h : Tuple 1 n) :
    loopColoringLLT h m = ∑ i : Fin m, (MvPolynomial.X i : XPoly m) := by
  classical
  have hsum : loopColoringLLT h m =
      ∑ κ : Fin 1 → Fin m, (MvPolynomial.X (κ 0) : XPoly m) := by
    letI : Unique (LoopCover h) :=
      ⟨inferInstance, fun L =>
        Subtype.ext (funext fun i => Subsingleton.elim _ _)⟩
    simp [loopColoringLLT, coloredLoopAscentCount,
      loopAscentEvents_singleton]
  let e : (Fin 1 → Fin m) ≃ Fin m :=
    { toFun := fun κ => κ 0
      invFun := fun i _ => i
      left_inv := by
        intro κ
        funext j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rfl
      right_inv := by
        intro i
        rfl }
  calc
    loopColoringLLT h m =
        ∑ κ : Fin 1 → Fin m, (MvPolynomial.X (κ 0) : XPoly m) := hsum
    _ = ∑ i : Fin m, (MvPolynomial.X i : XPoly m) := by
      simpa [e] using
        (Equiv.sum_comp e fun i : Fin m => (MvPolynomial.X i : XPoly m))

end VerticalStripLLT.CyclicHessenberg
