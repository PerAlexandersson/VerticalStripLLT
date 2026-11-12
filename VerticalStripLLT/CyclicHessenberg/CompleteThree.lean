import VerticalStripLLT.CyclicHessenberg.LayerListBridge
import VerticalStripLLT.CyclicHessenberg.ThreeVertexExpansion
import VerticalStripLLT.CyclicHessenberg.MatchingExpansion

set_option autoImplicit false

/-! The one-layer complete three-vertex expansion. -/

namespace VerticalStripLLT.CyclicHessenberg

def fullOrderOfList {k : ℕ} (l : List (Fin k))
    (hl : IsOrder (Finset.univ : Finset (Fin k)) l) : FullOrder k :=
  ⟨l, hl⟩

@[simp] theorem fullOrderOfList_val {k : ℕ} (l : List (Fin k))
    (hl : IsOrder (Finset.univ : Finset (Fin k)) l) : (fullOrderOfList l hl).val = l := rfl

def completeThree : Hessenberg 3 := Hessenberg.complete (by decide)

def completeThreeTuple : Tuple 3 1 := fun _ => completeThree

def completeThreeOrder210 : FullOrder 3 :=
  fullOrderOfList [2, 1, 0] (by unfold IsOrder; decide)

def completeThreeOrder201 : FullOrder 3 :=
  fullOrderOfList [2, 0, 1] (by unfold IsOrder; decide)

def completeThreeOrder021 : FullOrder 3 :=
  fullOrderOfList [0, 2, 1] (by unfold IsOrder; decide)

def completeThreeOrder120 : FullOrder 3 :=
  fullOrderOfList [1, 2, 0] (by unfold IsOrder; decide)

def completeThreeOrder102 : FullOrder 3 :=
  fullOrderOfList [1, 0, 2] (by unfold IsOrder; decide)

def completeThreeOrder012 : FullOrder 3 :=
  fullOrderOfList [0, 1, 2] (by unfold IsOrder; decide)

@[simp] theorem completeThreeOrder210_val : completeThreeOrder210.val = [2, 1, 0] := rfl
@[simp] theorem completeThreeOrder201_val : completeThreeOrder201.val = [2, 0, 1] := rfl
@[simp] theorem completeThreeOrder021_val : completeThreeOrder021.val = [0, 2, 1] := rfl
@[simp] theorem completeThreeOrder120_val : completeThreeOrder120.val = [1, 2, 0] := rfl
@[simp] theorem completeThreeOrder102_val : completeThreeOrder102.val = [1, 0, 2] := rfl
@[simp] theorem completeThreeOrder012_val : completeThreeOrder012.val = [0, 1, 2] := rfl

private theorem completeThree_kernel_eq_weight (π τ : FullOrder 3) :
    naturalOpenKernel completeThreeTuple π τ =
      layerListWeight completeThree Polynomial.X π.val τ.val := by
  have hprod : naturalOpenKernel completeThreeTuple =
      naturalLayerKernel completeThree := by
    simp [naturalOpenKernel, completeThreeTuple]
  rw [hprod]
  exact (layerListWeight_eq completeThree Polynomial.X π τ).symm

private theorem completeThreeKernel_210_210 :
    naturalOpenKernel completeThreeTuple completeThreeOrder210
      completeThreeOrder210 = 1 := by
  rw [completeThree_kernel_eq_weight]
  simp [layerListWeight, layerListFeasible, layerListAscentCount, spectatorCount,
    completeThree, Hessenberg.complete]

private theorem completeThreeKernel_210_201 :
    naturalOpenKernel completeThreeTuple completeThreeOrder210
      completeThreeOrder201 = 1 := by
  rw [completeThree_kernel_eq_weight]
  simp [layerListWeight, layerListFeasible, layerListAscentCount, spectatorCount,
    completeThree, Hessenberg.complete]

private theorem completeThreeKernel_201_021 :
    naturalOpenKernel completeThreeTuple completeThreeOrder201
      completeThreeOrder021 = 1 + Polynomial.X := by
  rw [completeThree_kernel_eq_weight]
  simp [layerListWeight, layerListFeasible, layerListAscentCount, spectatorCount,
    completeThree, Hessenberg.complete]

private theorem completeThreeKernel_210_120 :
    naturalOpenKernel completeThreeTuple completeThreeOrder210
      completeThreeOrder120 = 1 := by
  rw [completeThree_kernel_eq_weight]
  simp [layerListWeight, layerListFeasible, layerListAscentCount, spectatorCount,
    completeThree, Hessenberg.complete]

private theorem completeThreeKernel_210_102 :
    naturalOpenKernel completeThreeTuple completeThreeOrder210
      completeThreeOrder102 = 1 := by
  rw [completeThree_kernel_eq_weight]
  simp [layerListWeight, layerListFeasible, layerListAscentCount, spectatorCount,
    completeThree, Hessenberg.complete]

private theorem completeThreeKernel_201_012 :
    naturalOpenKernel completeThreeTuple completeThreeOrder201
      completeThreeOrder012 = 1 + Polynomial.X := by
  rw [completeThree_kernel_eq_weight]
  simp [layerListWeight, layerListFeasible, layerListAscentCount, spectatorCount,
    completeThree, Hessenberg.complete]

/-- The complete one-layer three-vertex expansion, with coefficients displayed. -/
theorem naturalCyclicExpansion_completeThree :
    naturalCyclicExpansion completeThreeTuple =
      natElementary 1 ^ 3 +
        MvPolynomial.C (Polynomial.X * (Polynomial.X + 3)) *
          natElementary 2 * natElementary 1 +
        MvPolynomial.C (Polynomial.X ^ 2 * (Polynomial.X + 2)) * natElementary 3 := by
  classical
  let Z : List (Fin 3) → List (Fin 3) → Polynomial ℕ :=
    kernelEntry (naturalOpenKernel completeThreeTuple)
  have h210210 : Z [2, 1, 0] [2, 1, 0] = 1 := by
    change kernelEntry (naturalOpenKernel completeThreeTuple)
      completeThreeOrder210.val completeThreeOrder210.val = 1
    rw [kernelEntry_order]
    exact completeThreeKernel_210_210
  have h210201 : Z [2, 1, 0] [2, 0, 1] = 1 := by
    change kernelEntry (naturalOpenKernel completeThreeTuple)
      completeThreeOrder210.val completeThreeOrder201.val = 1
    rw [kernelEntry_order]
    exact completeThreeKernel_210_201
  have h201021 : Z [2, 0, 1] [0, 2, 1] = 1 + Polynomial.X := by
    change kernelEntry (naturalOpenKernel completeThreeTuple)
      completeThreeOrder201.val completeThreeOrder021.val = 1 + Polynomial.X
    rw [kernelEntry_order]
    exact completeThreeKernel_201_021
  have h210120 : Z [2, 1, 0] [1, 2, 0] = 1 := by
    change kernelEntry (naturalOpenKernel completeThreeTuple)
      completeThreeOrder210.val completeThreeOrder120.val = 1
    rw [kernelEntry_order]
    exact completeThreeKernel_210_120
  have h210102 : Z [2, 1, 0] [1, 0, 2] = 1 := by
    change kernelEntry (naturalOpenKernel completeThreeTuple)
      completeThreeOrder210.val completeThreeOrder102.val = 1
    rw [kernelEntry_order]
    exact completeThreeKernel_210_102
  have h201012 : Z [2, 0, 1] [0, 1, 2] = 1 + Polynomial.X := by
    change kernelEntry (naturalOpenKernel completeThreeTuple)
      completeThreeOrder201.val completeThreeOrder012.val = 1 + Polynomial.X
    rw [kernelEntry_order]
    exact completeThreeKernel_201_012
  have hsupport :
      ({(2 : Fin 3), 1, 0} : Finset (Fin 3)) = Finset.univ := by
    ext x
    fin_cases x <;> simp
  have htriple := naturalKernelExpansion_triple (0 : Fin 3) 1 2
    (by decide) (by decide) Z
  rw [hsupport] at htriple
  rw [h210210, h210201, h201021, h210120, h210102, h201012] at htriple
  have hcoef2 : (Polynomial.X : Polynomial ℕ) * (1 + (1 + Polynomial.X) + 1) =
      Polynomial.X * (Polynomial.X + 3) := by
    ring
  have hcoef3 : (Polynomial.X : Polynomial ℕ) ^ 2 * (1 + (1 + Polynomial.X)) =
      Polynomial.X ^ 2 * (Polynomial.X + 2) := by
    ring
  rw [hcoef2, hcoef3] at htriple
  have hrec : naturalRecursiveCyclicExpansion completeThreeTuple =
      natElementary 1 ^ 3 +
        MvPolynomial.C (Polynomial.X * (Polynomial.X + 3)) *
          natElementary 2 * natElementary 1 +
        MvPolynomial.C (Polynomial.X ^ 2 * (Polynomial.X + 2)) * natElementary 3 := by
    change naturalKernelExpansion Finset.univ
      (kernelEntry (naturalOpenKernel completeThreeTuple)) = _
    simpa only [Z, map_one, one_mul] using htriple
  calc
    naturalCyclicExpansion completeThreeTuple =
        naturalCanonicalCyclicExpansion completeThreeTuple :=
      (naturalCanonicalCyclicExpansion_eq_matchingExpansion completeThreeTuple).symm
    _ = naturalRecursiveCyclicExpansion completeThreeTuple :=
      (naturalRecursiveCyclicExpansion_eq_cycleSum completeThreeTuple).symm
    _ = _ := hrec

end VerticalStripLLT.CyclicHessenberg
