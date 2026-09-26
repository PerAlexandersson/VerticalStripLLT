import VerticalStripLLT.Polynomial

namespace VerticalStripLLT

/-- Elementary base values with the conventional degree-zero value one. -/
noncomputable def elementaryNat : ℕ → EExpansion
  | 0 => 1
  | k + 1 => elementary k.succPNat

@[simp] theorem elementaryNat_zero : elementaryNat 0 = 1 := by rfl

@[simp] theorem elementaryNat_succ (k : ℕ) :
    elementaryNat (k + 1) = elementary k.succPNat := by rfl

@[simp] theorem evalElementary_elementaryNat (m k : ℕ) :
    evalElementary m (elementaryNat k) = MvPolynomial.esymm (Fin m) Q k := by
  cases k with
  | zero => simp
  | succ k => simp

end VerticalStripLLT
