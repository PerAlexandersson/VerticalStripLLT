import VerticalStripLLT.Components.FiniteMountainPeak
import VerticalStripLLT.Components.MountainScan
import VerticalStripLLT.Components.ComponentScalars

/-!
# Pairing the actual Cauchy product with the mountain scan

The accumulated prefix records the order of multiplication. Scalar coefficients
pass through a linear functional by scalar linearity; no multiplicativity of
that functional is required.
-/

namespace VerticalStripLLT.Components

open scoped BigOperators TensorProduct
open Classical

noncomputable section

variable {K : Type*} [CommRing K]

local instance scanPairingTensorRing (n : ℕ) : Ring (K ⊗[ℤ] WordAlgebra (Fin n)) :=
  Algebra.TensorProduct.instRing

private theorem linearEval_prefix_weightedWord {n : ℕ}
    (φ : K ⊗[ℤ] WordAlgebra (Fin n) →ₗ[K] K)
    (p w : List (Fin n)) (a : K) (Y : K ⊗[ℤ] WordAlgebra (Fin n)) :
    φ ((scalarWord K p * (a ⊗ₜ[ℤ] algebraWord w)) * Y) =
      a * φ (scalarWord K (p ++ w) * Y) := by
  have htmul : a ⊗ₜ[ℤ] algebraWord w = a • scalarWord K w := by
    simp [scalarWord, TensorProduct.smul_tmul', smul_eq_mul]
  rw [htmul, mul_smul_comm, ← scalarWord_append, smul_mul_assoc, map_smul, smul_eq_mul]

/-- Any scalar-linear functional pairs the Cauchy product with the literal mountain scan. -/
theorem linearEval_cauchyProduct {n : ℕ}
    (φ : K ⊗[ℤ] WordAlgebra (Fin n) →ₗ[K] K)
    (xs : List K) (p : List (Fin n)) (k : ℕ) (hk : k ≤ n) :
    φ (scalarWord K p *
      cauchyProduct (finiteLetter (K := K) n) (scalarAlphabet xs n) k) =
      mountainScan (elementaryScalar xs) n k (fun w => φ (scalarWord K (p ++ w))) := by
  induction k generalizing p with
  | zero => simp [cauchyProduct, mountainScan]
  | succ k ih =>
    have hkn : k < n := by lia
    have hkle : k ≤ n := hkn.le
    have hlength : (scalarAlphabet xs n).length = xs.length := by simp [scalarAlphabet]
    rw [cauchyProduct, hlength, finiteMountainPeak xs n k hkn]
    rw [← mul_assoc, mul_add, mul_one, add_mul, map_add]
    simp only [Finset.mul_sum, Finset.sum_mul, map_sum]
    simp_rw [linearEval_prefix_weightedWord]
    simp only [mountainScan, dif_pos hkn]
    rw [ih p hkle]
    congr 1
    apply Finset.sum_congr rfl
    intro B hB
    apply Finset.sum_congr rfl
    intro T hT
    rw [ih (p ++ blockWord (insert (⟨k, hkn⟩ : Fin n) B) T) hkle]
    congr 1
    apply mountainScan_congr
    intro w
    rw [List.append_assoc]

/-- The specialization is the actual component word count, with its original prefix. -/
theorem componentScalarEval_cauchyProduct_scan {n : ℕ} {D : Circular.Diagram n}
    (θ : Circular.Orientation D)
    (hforward : ∀ e : Circular.Edge D.area, e.tail < e.head)
    (xs : List K) (p : List (Fin n)) (k : ℕ) (hk : k ≤ n) :
    componentScalarEval K θ hforward
        (scalarWord K p *
          cauchyProduct (finiteLetter (K := K) n) (scalarAlphabet xs n) k) =
      mountainScan (elementaryScalar xs) n k
        (fun w => algebraMap ℤ K (componentWordCount D θ (p ++ w))) := by
  simpa only [componentScalarEval_scalarWord] using
    linearEval_cauchyProduct (componentScalarEval K θ hforward) xs p k hk

end

end VerticalStripLLT.Components
