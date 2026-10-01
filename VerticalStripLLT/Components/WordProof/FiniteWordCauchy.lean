import VerticalStripLLT.Components.WordProof.CauchyStep
import VerticalStripLLT.Components.WordProof.WordScalars

/-! Finite alphabet Cauchy factorization in the scalar word algebra. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Components

open scoped TensorProduct

noncomputable section

variable {K : Type*} [CommRing K]

local instance finiteWordTensorRing (N : ℕ) : Ring (K ⊗[ℤ] WordAlgebra (Fin N)) :=
  Algebra.TensorProduct.instRing

/-- The word letter indexed by `i`, with out-of-range indices sent to zero. -/
def finiteLetter (N : ℕ) (i : ℕ) :
    K ⊗[ℤ] WordAlgebra (Fin N) := by
  classical
  exact if hi : i < N then scalarWord (V := Fin N) K [⟨i, hi⟩] else 0

theorem finiteLetter_sandwich (N i : ℕ)
    (Y : K ⊗[ℤ] WordAlgebra (Fin N)) :
    finiteLetter (K := K) N i * Y * finiteLetter (K := K) N i = 0 := by
  classical
  by_cases hi : i < N
  · simp only [finiteLetter, dite_eq_left hi]
    exact scalarWord_sandwich (V := Fin N) K ⟨i, hi⟩ Y
  · simp [finiteLetter, hi]

theorem finiteLetter_triple (N j i k : ℕ)
    (hji : j < i) (hik : i < k) :
    finiteLetter (K := K) N i * (finiteLetter (K := K) N j * finiteLetter (K := K) N k -
        finiteLetter (K := K) N k * finiteLetter (K := K) N j) -
      (finiteLetter (K := K) N j * finiteLetter (K := K) N k -
        finiteLetter (K := K) N k * finiteLetter (K := K) N j) * finiteLetter (K := K) N i = 0 := by
  classical
  by_cases hj : j < N <;> by_cases hi : i < N <;> by_cases hk : k < N
  · simp only [finiteLetter, dite_eq_left hj, dite_eq_left hi, dite_eq_left hk]
    exact scalarWord_triple (V := Fin N) K ⟨j, hj⟩ ⟨i, hi⟩ ⟨k, hk⟩ hji hik
  all_goals simp [finiteLetter, hj, hi, hk]

/-- Lift a finite scalar alphabet into the scalar word algebra. -/
def scalarAlphabet (xs : List K) (N : ℕ) :
    List (K ⊗[ℤ] WordAlgebra (Fin N)) :=
  xs.map (fun x => algebraMap K (K ⊗[ℤ] WordAlgebra (Fin N)) x)

theorem scalarAlphabet_commute (xs : List K) (N : ℕ) (t : K)
    (ht : t ∈ xs) (Y : K ⊗[ℤ] WordAlgebra (Fin N)) :
    Commute (algebraMap K (K ⊗[ℤ] WordAlgebra (Fin N)) t) Y := by
  exact scalarWord_algebraMap_commutes (V := Fin N) K t Y

/-- The finite ordered Cauchy identity after scalar extension. -/
theorem finiteWordCauchy (xs : List K) (N d : ℕ) :
    colorProduct (finiteLetter (K := K) N) (scalarAlphabet xs N) d =
      cauchyProduct (finiteLetter (K := K) N) (scalarAlphabet xs N) d := by
  apply colorProduct_eq_cauchyProduct
  · exact finiteLetter_sandwich (K := K) N
  · exact finiteLetter_triple (K := K) N
  · intro t ht Y
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact scalarAlphabet_commute xs N s hs Y

end

end VerticalStripLLT.Components
