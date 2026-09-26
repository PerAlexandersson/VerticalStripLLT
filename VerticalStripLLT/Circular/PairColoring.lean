import VerticalStripLLT.Polynomial
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi

/-! Coloring weights for an arbitrary finite directed pair graph. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators

structure PairGraph (n : ℕ) where
  normalEdges : Finset (Fin n × Fin n)
  strictEdges : Finset (Fin n × Fin n)

namespace PairGraph

def admissible {n m : ℕ} (G : PairGraph n) (c : Fin n → Fin m) : Prop :=
  ∀ e ∈ G.strictEdges, c e.1 < c e.2

def ascentCount {n m : ℕ} (G : PairGraph n) (c : Fin n → Fin m) : ℕ :=
  (G.normalEdges.filter fun e => c e.1 < c e.2).card

noncomputable def coloringWeight {n m : ℕ} (G : PairGraph n) (c : Fin n → Fin m) : XPoly m := by
  classical
  exact if admissible G c then
    MvPolynomial.C (Polynomial.X ^ ascentCount G c) * ∏ v, MvPolynomial.X (c v)
  else 0

noncomputable def coloringLLT {n : ℕ} (G : PairGraph n) (m : ℕ) : XPoly m :=
  ∑ c : Fin n → Fin m, coloringWeight G c

end PairGraph

end VerticalStripLLT.Circular
