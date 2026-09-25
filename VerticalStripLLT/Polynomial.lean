import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-! Finite alphabets and a separate algebra of formal elementary expressions. -/

namespace VerticalStripLLT

abbrev Q := Polynomial ℤ
abbrev XPoly (m : ℕ) := MvPolynomial (Fin m) Q

/-- Finite elementary expressions; generator `k` has weighted degree `k`. -/
abbrev EExpansion := MvPolynomial ℕ+ Q

noncomputable def elementary (k : ℕ+) : EExpansion := MvPolynomial.X k

/-- Interpret formal elementary generators in a fixed finite alphabet. -/
noncomputable def evalElementary (m : ℕ) : EExpansion →+* XPoly m :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun k => MvPolynomial.esymm (Fin m) Q k.val)

@[simp] theorem evalElementary_C (m : ℕ) (p : Q) :
    evalElementary m (MvPolynomial.C p) = MvPolynomial.C p := by
  simp [evalElementary]

@[simp] theorem evalElementary_elementary (m : ℕ) (k : ℕ+) :
    evalElementary m (elementary k) = MvPolynomial.esymm (Fin m) Q k.val := by
  simp [evalElementary, elementary]

end VerticalStripLLT
