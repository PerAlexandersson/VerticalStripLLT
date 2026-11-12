import VerticalStripLLT.Polynomial
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange

set_option autoImplicit false

/-! Elementary weights of a finite list of color variables. -/

namespace VerticalStripLLT.CyclicHessenberg

/-- The degree-`d` elementary weight of the entries of a finite list. -/
def elementaryWeights {R : Type*} [CommSemiring R] (Y : List R) (d : ℕ) : R :=
  (Y : Multiset R).esymm d

@[simp] theorem elementaryWeights_zero {R : Type*} [CommSemiring R] (Y : List R) :
    elementaryWeights Y 0 = 1 := by
  simp [elementaryWeights]

@[simp] theorem elementaryWeights_nil_succ {R : Type*} [CommSemiring R] (d : ℕ) :
    elementaryWeights ([] : List R) (d + 1) = 0 := by
  apply Multiset.esymm_of_card_lt
  simp

/-- Adding one list entry gives the usual elementary-symmetric recurrence. -/
theorem elementaryWeights_cons_succ {R : Type*} [CommSemiring R] (t : R)
    (Y : List R) (d : ℕ) :
    elementaryWeights (t :: Y) (d + 1) =
      elementaryWeights Y (d + 1) + t * elementaryWeights Y d := by
  classical
  change (t ::ₘ (Y : Multiset R)).esymm (d + 1) = _
  simp [elementaryWeights, Multiset.esymm, Multiset.powersetCard_cons,
    Multiset.map_add, Multiset.map_map, Multiset.prod_cons,
    Multiset.sum_map_mul_left]

/-- The list of finite-alphabet variables has the standard elementary weight. -/
theorem elementaryWeights_X (m d : ℕ) :
    elementaryWeights
        (List.ofFn (fun i : Fin m => (MvPolynomial.X i : XPoly m))) d =
      MvPolynomial.esymm (Fin m) Q d := by
  classical
  have hfin : (List.finRange m : Multiset (Fin m)) = Finset.univ.val := by
    rw [← Fin.sort_univ m]
    exact Finset.sort_eq
  have hX :
      (List.ofFn (fun i : Fin m => (MvPolynomial.X i : XPoly m)) :
        Multiset (XPoly m)) = Finset.univ.val.map MvPolynomial.X := by
    rw [List.ofFn_eq_map]
    change (List.finRange m : Multiset (Fin m)).map MvPolynomial.X = _
    rw [hfin]
  rw [elementaryWeights, hX, MvPolynomial.esymm_eq_multiset_esymm]

end VerticalStripLLT.CyclicHessenberg
