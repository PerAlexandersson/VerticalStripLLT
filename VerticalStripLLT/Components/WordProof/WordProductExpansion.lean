import VerticalStripLLT.Components.WordProof.WordScalars
import VerticalStripLLT.Components.WordProof.ComponentScalars
import Mathlib.Data.List.Sublists
import Mathlib.Algebra.BigOperators.Ring.List

/-! Finite ordered products expand into weighted subwords without commutativity. -/

namespace VerticalStripLLT.Components

open scoped TensorProduct

noncomputable section

variable {I R : Type*} [Semiring R]

/-- The order of each selected subword is the original order of the factors. -/
theorem list_prod_one_add_eq_sum_subwords (L : List I) (f : I → R) :
    (L.map (fun i => 1 + f i)).prod =
      (L.sublists'.map (fun S => (S.map f).prod)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, List.sublists'_cons,
      List.map_append, List.sum_append, List.map_map, Function.comp_def, ih]
    rw [List.sum_map_mul_left]
    rw [add_mul, one_mul]

variable {V K : Type*} [LinearOrder V] [CommRing K]

local instance productExpansionTensorRing : Ring (K ⊗[ℤ] WordAlgebra V) :=
  Algebra.TensorProduct.instRing

@[simp]
theorem algebraWord_nil : algebraWord ([] : List V) = 1 := by
  change wordProjection (1 : WordRing V) = 1
  exact map_one wordProjection

/-- Products of scalar-weighted letters concatenate their words. -/
theorem prod_weighted_letters (L : List I) (weight : I → K) (letter : I → V) :
    (L.map (fun i => weight i ⊗ₜ[ℤ] algebraWord [letter i])).prod =
      (L.map weight).prod ⊗ₜ[ℤ] algebraWord (L.map letter) := by
  induction L with
  | nil => simp [Algebra.TensorProduct.one_def]
  | cons i L ih =>
    simp only [List.map_cons, List.prod_cons, ih, Algebra.TensorProduct.tmul_mul_tmul]
    rw [← algebraWord_append]
    rfl

/-- This explicit subword sum is the finite expansion used by the coloring bridge. -/
theorem prod_one_add_weighted_letters (L : List I) (weight : I → K) (letter : I → V) :
    (L.map (fun i => 1 + weight i ⊗ₜ[ℤ] algebraWord [letter i])).prod =
      (L.sublists'.map (fun S =>
        (S.map weight).prod ⊗ₜ[ℤ] algebraWord (S.map letter))).sum := by
  rw [list_prod_one_add_eq_sum_subwords]
  simp_rw [prod_weighted_letters]

/-- Pairing an ordered product gives the exact weighted actual-component word counts. -/
theorem componentScalarEval_prod_one_add {n : ℕ} {D : Circular.Diagram n}
    (θ : Circular.Orientation D)
    (hforward : ∀ e : Circular.Edge D.area, e.tail < e.head)
    (L : List I) (weight : I → K) (letter : I → Fin n) :
    componentScalarEval K θ hforward
        ((L.map (fun i => 1 + weight i ⊗ₜ[ℤ] algebraWord [letter i])).prod) =
      (L.sublists'.map (fun S => (S.map weight).prod *
        algebraMap ℤ K (componentWordCount D θ (S.map letter)))).sum := by
  rw [prod_one_add_weighted_letters, ← List.sum_hom]
  simp only [List.map_map, Function.comp_def, componentScalarEval_tmul_algebraWord]

end

end VerticalStripLLT.Components
