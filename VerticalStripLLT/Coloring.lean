import VerticalStripLLT.Path
import VerticalStripLLT.Polynomial
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi

/-! The coloring definition, independently of any recursive construction. -/

namespace VerticalStripLLT

open scoped BigOperators

def admissible {n m : ℕ} (P : SchroderPath n) (c : Fin n → Fin m) : Prop :=
  ∀ e ∈ P.strictEdges, c e.1 < c e.2

def ascentCount {n m : ℕ} (P : SchroderPath n) (c : Fin n → Fin m) : ℕ :=
  (P.normalEdges.filter fun e => c e.1 < c e.2).card

noncomputable def coloringWeight {n m : ℕ} (P : SchroderPath n)
    (c : Fin n → Fin m) : XPoly m := by
  classical
  exact if admissible P c then
    MvPolynomial.C (Polynomial.X ^ ascentCount P c) * ∏ v, MvPolynomial.X (c v)
  else 0

/-- The manuscript's coloring LLT specialized to `m` colors (including `m = 0`). -/
noncomputable def coloringLLT {n : ℕ} (P : SchroderPath n) (m : ℕ) : XPoly m :=
  ∑ c : Fin n → Fin m, coloringWeight P c

end VerticalStripLLT
