import VerticalStripLLT.CyclicHessenberg.Data
import VerticalStripLLT.CyclicHessenberg.Kernel
import VerticalStripLLT.OrientationShift
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Matrix.Basic

set_option autoImplicit false

/-! Finite layer weights and their ordered transfer-matrix products. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

/-- A full boundary order on the vertices of a finite layer. -/
abbrev FullOrder (k : ℕ) := Order (Finset.univ : Finset (Fin k))

/-- The positions in a full boundary order, retaining the cardinality expression. -/
abbrev LayerPosition (k : ℕ) := Fin ((Finset.univ : Finset (Fin k)).card)

/-- Every vertex in a starting order has an allowed edge to its matched endpoint. -/
def layerFeasible {k : ℕ} (h : Hessenberg k) (π τ : FullOrder k) : Prop :=
  ∀ i : LayerPosition k, (orderEquiv π i).val ≤ h (orderEquiv τ i).val

/-- Potential ascent events in one layer, indexed by their two positions. -/
noncomputable def layerAscentEvents {k : ℕ} (h : Hessenberg k)
    (π τ : FullOrder k) : Finset (LayerPosition k × LayerPosition k) := by
  classical
  exact Finset.univ.filter fun e =>
    e.1 < e.2 ∧
      (orderEquiv π e.1).val < (orderEquiv π e.2).val ∧
      (orderEquiv π e.2).val ≤ h (orderEquiv τ e.1).val

/-- The number of layer ascent events. -/
noncomputable def layerAscentCount {k : ℕ} (h : Hessenberg k)
    (π τ : FullOrder k) : ℕ := (layerAscentEvents h π τ).card

/-- A generic layer kernel over any commutative semiring. -/
noncomputable def layerKernelAt {k : ℕ} {R : Type*} [CommSemiring R]
    (h : Hessenberg k) (z : R) : Kernel R (Finset.univ : Finset (Fin k)) := by
  classical
  exact fun π τ =>
    if layerFeasible h π τ then z ^ layerAscentCount h π τ else 0

/-- Coefficient homomorphisms commute with evaluation of the layer kernel. -/
theorem layerKernelAt_map {k : ℕ} {R S : Type*} [CommSemiring R] [CommSemiring S]
    (h : Hessenberg k) (f : R →+* S) (z : R) :
    f.mapMatrix (layerKernelAt h z) = layerKernelAt h (f z) := by
  classical
  funext π τ
  by_cases hf : layerFeasible h π τ <;> simp [layerKernelAt, hf]

/-- The raw layer kernel, weighted by `q` to the ascent count. -/
noncomputable def rawLayerKernel {k : ℕ} (h : Hessenberg k) :
    Kernel Q (Finset.univ : Finset (Fin k)) :=
  layerKernelAt h Polynomial.X

/-- The natural layer kernel, already weighted by `(1+q)` to the ascent count. -/
noncomputable def naturalLayerKernel {k : ℕ} (h : Hessenberg k) :
    Kernel (Polynomial ℕ) (Finset.univ : Finset (Fin k)) :=
  layerKernelAt h (1 + Polynomial.X)

/-- Cast coefficients from natural polynomials to integer polynomials. -/
noncomputable def naturalPolynomialCast : Polynomial ℕ →+* Q :=
  Polynomial.mapRingHom (Nat.castRingHom ℤ)

/-- Casting the natural layer agrees with shifting the raw layer by `q ↦ q+1`. -/
theorem cast_naturalLayerKernel_eq_shift_rawLayerKernel {k : ℕ} (h : Hessenberg k) :
    naturalPolynomialCast.mapMatrix (naturalLayerKernel h) =
      VerticalStripLLT.qShift.mapMatrix (rawLayerKernel h) := by
  have harg : naturalPolynomialCast (1 + Polynomial.X) =
      VerticalStripLLT.qShift Polynomial.X := by
    simp [naturalPolynomialCast, VerticalStripLLT.qShift,
      Polynomial.coe_compRingHom_apply, Polynomial.X_comp, add_comm]
  calc
    naturalPolynomialCast.mapMatrix (naturalLayerKernel h) =
        layerKernelAt h (naturalPolynomialCast (1 + Polynomial.X)) :=
      layerKernelAt_map h naturalPolynomialCast (1 + Polynomial.X)
    _ = layerKernelAt h (VerticalStripLLT.qShift Polynomial.X) := by rw [harg]
    _ = VerticalStripLLT.qShift.mapMatrix (rawLayerKernel h) :=
      (layerKernelAt_map h VerticalStripLLT.qShift Polynomial.X).symm

/-- The natural layer product in increasing layer order, with rows as starts
and columns as ends. -/
noncomputable def naturalOpenKernel {k n : ℕ} (h : Tuple k n) :
    Kernel (Polynomial ℕ) (Finset.univ : Finset (Fin k)) :=
  (List.ofFn fun i : Fin n => naturalLayerKernel (h i)).prod

/-- The ordered product of the raw layer kernels. -/
noncomputable def rawOpenKernel {k n : ℕ} (h : Tuple k n) :
    Kernel Q (Finset.univ : Finset (Fin k)) :=
  (List.ofFn fun i : Fin n => rawLayerKernel (h i)).prod

/-- The recursive finite sum over all intermediate boundary orders, with the
left endpoint as the row and the right endpoint as the column. -/
noncomputable def layerPathSum {k : ℕ} {R : Type*} [Semiring R]
    (layers : List (Kernel R (Finset.univ : Finset (Fin k))))
    (π τ : FullOrder k) : R :=
  match layers with
  | [] => if π = τ then 1 else 0
  | M :: rest => ∑ μ : FullOrder k, M π μ * layerPathSum rest μ τ

/-- Matrix-product entries are the finite sums over intermediate boundary orders. -/
theorem layerPathSum_eq_prod {k : ℕ} {R : Type*} [Semiring R]
    (layers : List (Kernel R (Finset.univ : Finset (Fin k))))
    (π τ : FullOrder k) :
    layerPathSum layers π τ = layers.prod π τ := by
  induction layers generalizing π with
  | nil => simp [layerPathSum, Matrix.one_apply]
  | cons M rest ih =>
    simp only [layerPathSum, List.prod_cons, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro μ hμ
    rw [ih]

/-- The entry of the natural open kernel is its intermediate-order path sum. -/
theorem naturalOpenKernel_entry_eq_sum {k n : ℕ} (h : Tuple k n)
    (π τ : FullOrder k) :
    naturalOpenKernel h π τ =
      layerPathSum (List.ofFn fun i : Fin n => naturalLayerKernel (h i)) π τ := by
  exact (layerPathSum_eq_prod _ π τ).symm

/-- Casting the ordered natural product is the shift of the raw ordered product. -/
theorem cast_naturalOpenKernel_eq_shift_rawOpenKernel {k n : ℕ} (h : Tuple k n) :
    naturalPolynomialCast.mapMatrix (naturalOpenKernel h) =
      VerticalStripLLT.qShift.mapMatrix (rawOpenKernel h) := by
  classical
  change naturalPolynomialCast.mapMatrix
      ((List.ofFn fun i : Fin n => naturalLayerKernel (h i)).prod) =
    VerticalStripLLT.qShift.mapMatrix
      ((List.ofFn fun i : Fin n => rawLayerKernel (h i)).prod)
  rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact cast_naturalLayerKernel_eq_shift_rawLayerKernel (h i)

end VerticalStripLLT.CyclicHessenberg
