import VerticalStripLLT.CyclicHessenberg.CompleteThree

set_option autoImplicit false

/-! The two-layer Kim--Oh Example 6.7. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

def kimOhHessenberg : Hessenberg 3 where
  toFun i := if i.val = 0 then 0 else 2
  monotone' := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  le_apply' := by
    intro i
    fin_cases i <;> decide

def kimOhTuple : Tuple 3 2 := fun _ => kimOhHessenberg

private theorem fullOrderThree_val_cases (π : FullOrder 3) :
    π.val = [0, 1, 2] ∨ π.val = [0, 2, 1] ∨
      π.val = [1, 0, 2] ∨ π.val = [1, 2, 0] ∨
      π.val = [2, 0, 1] ∨ π.val = [2, 1, 0] := by
  have hlen : π.val.length = 3 := by simpa using π.property.length
  obtain ⟨x, y, z, hxyz⟩ := List.length_eq_three.mp hlen
  have hnodup : ([x, y, z] : List (Fin 3)).Nodup := by
    rw [← hxyz]
    exact π.property.1
  rw [hxyz]
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all

private def fullOrderThreeEquiv : FullOrder 3 ≃ Fin 6 where
  toFun π :=
    if π.val = [0, 1, 2] then 0 else
    if π.val = [0, 2, 1] then 1 else
    if π.val = [1, 0, 2] then 2 else
    if π.val = [1, 2, 0] then 3 else
    if π.val = [2, 0, 1] then 4 else 5
  invFun i := match i.val with
    | 0 => completeThreeOrder012
    | 1 => completeThreeOrder021
    | 2 => completeThreeOrder102
    | 3 => completeThreeOrder120
    | 4 => completeThreeOrder201
    | _ => completeThreeOrder210
  left_inv π := by
    rcases fullOrderThree_val_cases π with h | h | h | h | h | h
    all_goals apply Subtype.ext <;> simp [h]
  right_inv i := by
    fin_cases i <;> simp

private theorem sum_fullOrder_three {R : Type*} [AddCommMonoid R]
    (F : FullOrder 3 → R) :
    (∑ π : FullOrder 3, F π) =
      F completeThreeOrder012 +
        (F completeThreeOrder021 +
          (F completeThreeOrder102 +
            (F completeThreeOrder120 +
              (F completeThreeOrder201 + F completeThreeOrder210)))) := by
  classical
  calc
    (∑ π : FullOrder 3, F π) =
        ∑ i : Fin 6, F (fullOrderThreeEquiv.symm i) :=
      (Equiv.sum_comp fullOrderThreeEquiv.symm F).symm
    _ = _ := by simp [fullOrderThreeEquiv, Fin.sum_univ_succ]

private theorem kimOhLayer_eq_listWeight (π τ : FullOrder 3) :
    naturalLayerKernel kimOhHessenberg π τ =
      layerListWeight kimOhHessenberg Polynomial.X π.val τ.val :=
  (layerListWeight_eq kimOhHessenberg Polynomial.X π τ).symm

private theorem kimOhOpenKernel_entry_eq_sum (π τ : FullOrder 3) :
    naturalOpenKernel kimOhTuple π τ =
      ∑ μ : FullOrder 3,
        naturalLayerKernel kimOhHessenberg π μ *
          naturalLayerKernel kimOhHessenberg μ τ := by
  classical
  have hlist :
      List.ofFn (fun i : Fin 2 => naturalLayerKernel (kimOhTuple i)) =
        [naturalLayerKernel kimOhHessenberg, naturalLayerKernel kimOhHessenberg] := by
    simp [kimOhTuple, List.ofFn_succ]
  rw [naturalOpenKernel, hlist]
  simp only [List.prod_cons, List.prod_nil, mul_one, Matrix.mul_apply]

private theorem kimOhKernel_210_210 :
    naturalOpenKernel kimOhTuple completeThreeOrder210 completeThreeOrder210 =
      Polynomial.X + 2 := by
  rw [kimOhOpenKernel_entry_eq_sum, sum_fullOrder_three]
  simp [kimOhLayer_eq_listWeight, layerListWeight, layerListFeasible,
    layerListAscentCount, spectatorCount, kimOhHessenberg,
    completeThreeOrder210_val, completeThreeOrder201_val, completeThreeOrder120_val,
    completeThreeOrder012_val, completeThreeOrder021_val, completeThreeOrder102_val]
  ring

private theorem kimOhKernel_210_201 :
    naturalOpenKernel kimOhTuple completeThreeOrder210 completeThreeOrder201 = 0 := by
  rw [kimOhOpenKernel_entry_eq_sum, sum_fullOrder_three]
  simp [kimOhLayer_eq_listWeight, layerListWeight, layerListFeasible,
    layerListAscentCount, spectatorCount, kimOhHessenberg,
    completeThreeOrder210_val, completeThreeOrder201_val, completeThreeOrder120_val,
    completeThreeOrder012_val, completeThreeOrder021_val, completeThreeOrder102_val]

private theorem kimOhKernel_201_021 :
    naturalOpenKernel kimOhTuple completeThreeOrder201 completeThreeOrder021 = 0 := by
  rw [kimOhOpenKernel_entry_eq_sum, sum_fullOrder_three]
  simp [kimOhLayer_eq_listWeight, layerListWeight, layerListFeasible,
    layerListAscentCount, spectatorCount, kimOhHessenberg,
    completeThreeOrder210_val, completeThreeOrder201_val, completeThreeOrder120_val,
    completeThreeOrder012_val, completeThreeOrder021_val, completeThreeOrder102_val]

private theorem kimOhKernel_210_120 :
    naturalOpenKernel kimOhTuple completeThreeOrder210 completeThreeOrder120 =
      Polynomial.X + 2 := by
  rw [kimOhOpenKernel_entry_eq_sum, sum_fullOrder_three]
  simp [kimOhLayer_eq_listWeight, layerListWeight, layerListFeasible,
    layerListAscentCount, spectatorCount, kimOhHessenberg,
    completeThreeOrder210_val, completeThreeOrder201_val, completeThreeOrder120_val,
    completeThreeOrder012_val, completeThreeOrder021_val, completeThreeOrder102_val]
  ring

private theorem kimOhKernel_210_102 :
    naturalOpenKernel kimOhTuple completeThreeOrder210 completeThreeOrder102 = 0 := by
  rw [kimOhOpenKernel_entry_eq_sum, sum_fullOrder_three]
  simp [kimOhLayer_eq_listWeight, layerListWeight, layerListFeasible,
    layerListAscentCount, spectatorCount, kimOhHessenberg,
    completeThreeOrder210_val, completeThreeOrder201_val, completeThreeOrder120_val,
    completeThreeOrder012_val, completeThreeOrder021_val, completeThreeOrder102_val]

private theorem kimOhKernel_201_012 :
    naturalOpenKernel kimOhTuple completeThreeOrder201 completeThreeOrder012 = 0 := by
  rw [kimOhOpenKernel_entry_eq_sum, sum_fullOrder_three]
  simp [kimOhLayer_eq_listWeight, layerListWeight, layerListFeasible,
    layerListAscentCount, spectatorCount, kimOhHessenberg,
    completeThreeOrder210_val, completeThreeOrder201_val, completeThreeOrder120_val,
    completeThreeOrder012_val, completeThreeOrder021_val, completeThreeOrder102_val]

/-- The two-layer Hessenberg kernel from Kim--Oh, Example 6.7. -/
theorem naturalCyclicExpansion_kimOh_example67 :
    naturalCyclicExpansion kimOhTuple =
      MvPolynomial.C (Polynomial.X + 2) * natElementary 1 ^ 3 +
        MvPolynomial.C (Polynomial.X * (Polynomial.X + 2)) *
          natElementary 2 * natElementary 1 := by
  classical
  let Z : List (Fin 3) → List (Fin 3) → Polynomial ℕ :=
    kernelEntry (naturalOpenKernel kimOhTuple)
  have h210210 : Z [2, 1, 0] [2, 1, 0] = Polynomial.X + 2 := by
    change kernelEntry (naturalOpenKernel kimOhTuple)
      completeThreeOrder210.val completeThreeOrder210.val = _
    rw [kernelEntry_order]
    exact kimOhKernel_210_210
  have h210201 : Z [2, 1, 0] [2, 0, 1] = 0 := by
    change kernelEntry (naturalOpenKernel kimOhTuple)
      completeThreeOrder210.val completeThreeOrder201.val = 0
    rw [kernelEntry_order]
    exact kimOhKernel_210_201
  have h201021 : Z [2, 0, 1] [0, 2, 1] = 0 := by
    change kernelEntry (naturalOpenKernel kimOhTuple)
      completeThreeOrder201.val completeThreeOrder021.val = 0
    rw [kernelEntry_order]
    exact kimOhKernel_201_021
  have h210120 : Z [2, 1, 0] [1, 2, 0] = Polynomial.X + 2 := by
    change kernelEntry (naturalOpenKernel kimOhTuple)
      completeThreeOrder210.val completeThreeOrder120.val = _
    rw [kernelEntry_order]
    exact kimOhKernel_210_120
  have h210102 : Z [2, 1, 0] [1, 0, 2] = 0 := by
    change kernelEntry (naturalOpenKernel kimOhTuple)
      completeThreeOrder210.val completeThreeOrder102.val = 0
    rw [kernelEntry_order]
    exact kimOhKernel_210_102
  have h201012 : Z [2, 0, 1] [0, 1, 2] = 0 := by
    change kernelEntry (naturalOpenKernel kimOhTuple)
      completeThreeOrder201.val completeThreeOrder012.val = 0
    rw [kernelEntry_order]
    exact kimOhKernel_201_012
  have hsupport :
      ({(2 : Fin 3), 1, 0} : Finset (Fin 3)) = Finset.univ := by
    ext x
    fin_cases x <;> simp
  have htriple := naturalKernelExpansion_triple (0 : Fin 3) 1 2
    (by decide) (by decide) Z
  rw [hsupport] at htriple
  rw [h210210, h210201, h201021, h210120, h210102, h201012] at htriple
  have hcoeff : (Polynomial.X : Polynomial ℕ) * (0 + 0 + (Polynomial.X + 2)) =
      Polynomial.X * (Polynomial.X + 2) := by ring
  have hcoeff3 : (Polynomial.X : Polynomial ℕ) ^ 2 * (0 + 0) = 0 := by ring
  rw [hcoeff, hcoeff3] at htriple
  simp only [map_zero, zero_mul, add_zero] at htriple
  have hrec : naturalRecursiveCyclicExpansion kimOhTuple =
      MvPolynomial.C (Polynomial.X + 2) * natElementary 1 ^ 3 +
        MvPolynomial.C (Polynomial.X * (Polynomial.X + 2)) *
          natElementary 2 * natElementary 1 := by
    change naturalKernelExpansion Finset.univ
      (kernelEntry (naturalOpenKernel kimOhTuple)) = _
    simpa only [Z] using htriple
  calc
    naturalCyclicExpansion kimOhTuple = naturalCanonicalCyclicExpansion kimOhTuple :=
      (naturalCanonicalCyclicExpansion_eq_matchingExpansion kimOhTuple).symm
    _ = naturalRecursiveCyclicExpansion kimOhTuple :=
      (naturalRecursiveCyclicExpansion_eq_cycleSum kimOhTuple).symm
    _ = _ := hrec

end VerticalStripLLT.CyclicHessenberg
