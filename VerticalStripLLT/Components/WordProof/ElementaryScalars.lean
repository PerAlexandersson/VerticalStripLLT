import VerticalStripLLT.Components.WordProof.CauchyStep
import Mathlib.Algebra.BigOperators.Ring.Multiset
import VerticalStripLLT.Polynomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-! The finite list recursion for elementary coefficients agrees with the
multiset elementary symmetric function. -/

namespace VerticalStripLLT.Components

open scoped BigOperators

noncomputable section

variable {K : Type*} [CommRing K]

/-- The finite scalar coefficients commute with a ring homomorphism. -/
theorem elementaryScalar_map {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (xs : List R) (k : ℕ) :
    elementaryScalar (xs.map f) k = f (elementaryScalar xs k) := by
  induction xs generalizing k with
  | nil => cases k <;> simp [elementaryScalar]
  | cons t xs ih =>
    cases k <;> simp [elementaryScalar, ih]

theorem multiset_esymm_cons_succ (t : K) (s : Multiset K) (k : ℕ) :
    Multiset.esymm (t ::ₘ s) (k + 1) =
      Multiset.esymm s (k + 1) + t * Multiset.esymm s k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add,
    Multiset.sum_add, Multiset.map_map,
    Multiset.sum_map_mul_left]

theorem elementaryScalar_eq_multiset_esymm (xs : List K) (k : ℕ) :
    elementaryScalar xs k = Multiset.esymm (xs : Multiset K) k := by
  induction xs generalizing k with
  | nil =>
      cases k with
      | zero => simp [elementaryScalar]
      | succ k =>
        exact (Multiset.esymm_of_card_lt (by simp :
          (0 : Multiset K).card < k + 1)).symm
  | cons t xs ih =>
      cases k with
      | zero => simp [elementaryScalar, Multiset.esymm]
      | succ k =>
          change elementaryScalar xs (k + 1) + t * elementaryScalar xs k =
            Multiset.esymm (t ::ₘ (xs : Multiset K)) (k + 1)
          rw [ih (k + 1), ih k, multiset_esymm_cons_succ]

theorem elementaryScalar_ofFn_XPoly (m k : ℕ) :
    elementaryScalar
        (List.ofFn (fun i : Fin m =>
          (MvPolynomial.X i : XPoly m))) k =
      MvPolynomial.esymm (Fin m) Q k := by
  rw [elementaryScalar_eq_multiset_esymm]
  have h := congrFun
    (MvPolynomial.esymm_eq_multiset_esymm (σ := Fin m) (R := Q)) k
  simpa using h.symm

end

end VerticalStripLLT.Components
