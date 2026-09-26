import VerticalStripLLT.ElementaryColorings
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

/-! Algebra for colorings of a finite disjoint union of directed chains. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators

/-- The coloring sum for disjoint chains factors into elementary polynomials.

The chain indexed by `i` has `k i` vertices, ordered by `Fin (k i)`. -/
theorem sum_strictMono_sigma_colorings_eq_prod_esymm
    {I : Type*} [Fintype I] [DecidableEq I] (k : I → ℕ) (m : ℕ) :
    (∑ c : ((Σ i : I, Fin (k i)) → Fin m),
      if ∀ i, StrictMono (fun j => c ⟨i, j⟩) then
        ∏ v, MvPolynomial.X (c v)
      else 0) =
      ∏ i, MvPolynomial.esymm (Fin m) Q (k i) := by
  classical
  let curry : ((Σ i : I, Fin (k i)) → Fin m) ≃
      ((i : I) → Fin (k i) → Fin m) :=
    Equiv.piCurry (fun _ _ => Fin m)
  calc
    (∑ c : ((Σ i : I, Fin (k i)) → Fin m),
      if ∀ i, StrictMono (fun j => c ⟨i, j⟩) then
        ∏ v, MvPolynomial.X (c v)
      else 0) =
        ∑ f : ((i : I) → Fin (k i) → Fin m),
          if ∀ i, StrictMono (f i) then
            ∏ v : Σ i : I, Fin (k i), MvPolynomial.X (f v.1 v.2)
          else 0 := by
            refine Fintype.sum_equiv curry
              (fun c =>
                if ∀ i, StrictMono (fun j => c ⟨i, j⟩) then
                  ∏ v, MvPolynomial.X (c v)
                else 0)
              (fun f =>
                if ∀ i, StrictMono (f i) then
                  ∏ v : Σ i : I, Fin (k i), MvPolynomial.X (f v.1 v.2)
                else 0) ?_
            intro c
            rfl
    _ = ∑ f : ((i : I) → Fin (k i) → Fin m),
          ∏ i, if StrictMono (f i) then
            ∏ j, MvPolynomial.X (f i j)
          else 0 := by
            apply Finset.sum_congr rfl
            intro f _
            have hprod :
                (∏ v : Σ i : I, Fin (k i), (MvPolynomial.X (f v.1 v.2) : XPoly m)) =
                  ∏ i, ∏ j, MvPolynomial.X (f i j) := by
              rw [Fintype.prod_sigma]
            rw [hprod]
            exact (Fintype.prod_ite_zero (p := fun i => StrictMono (f i))
              (f := fun i => ∏ j, MvPolynomial.X (f i j))).symm
    _ = ∏ i, (∑ c : Fin (k i) → Fin m,
          if StrictMono c then ∏ j, MvPolynomial.X (c j) else 0) := by
            rw [Fintype.prod_sum]
    _ = ∏ i, MvPolynomial.esymm (Fin m) Q (k i) := by
            apply Finset.prod_congr rfl
            intro i _
            exact increasingColoringSum_eq_esymm (k i) m

end VerticalStripLLT.Circular
