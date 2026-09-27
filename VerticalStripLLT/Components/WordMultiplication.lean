import VerticalStripLLT.Components.WordContext
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.FreeMonoid.Basic

/-! Multiplication on the free word ring and stability of word relations. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {V : Type*}

abbrev WordRing (V : Type*) := MonoidAlgebra ℤ (FreeMonoid V)

/-- Coefficients identify the free word ring with the word module. -/
def wordCoefficients : WordRing V ≃ₗ[ℤ] WordModule V :=
  MonoidAlgebra.coeffLinearEquiv ℤ

/-- The monomial represented by a word. -/
def wordMonomial (w : List V) : WordRing V :=
  MonoidAlgebra.single (FreeMonoid.ofList w) 1

@[simp]
theorem wordCoefficients_wordMonomial (w : List V) :
    wordCoefficients (wordMonomial w) = basisWord w := by
  rfl

theorem wordCoefficients_context (ρ σ : List V) (x : WordRing V) :
    wordCoefficients (wordMonomial ρ * x * wordMonomial σ) =
    contextLinear ρ σ (wordCoefficients x) := by
  induction x using MonoidAlgebra.induction_on with
  | of m =>
    change wordCoefficients
        (wordMonomial ρ * MonoidAlgebra.single m 1 * wordMonomial σ) = _
    simp only [wordMonomial, MonoidAlgebra.single_mul_single, one_mul]
    change Finsupp.single (ρ ++ FreeMonoid.toList m ++ σ) 1 =
      contextLinear ρ σ (basisWord (FreeMonoid.toList m))
    exact (contextLinear_basisWord ρ σ (FreeMonoid.toList m)).symm
  | add x y hx hy =>
    simp only [mul_add, add_mul, map_add, hx, hy]
  | smul r x hx =>
    simp only [mul_smul_comm, smul_mul_assoc, map_smul, hx]

theorem wordCoefficients_left_context (ρ : List V) (x : WordRing V) :
    wordCoefficients (wordMonomial ρ * x) =
    contextLinear ρ [] (wordCoefficients x) := by
  simpa [wordMonomial, FreeMonoid.ofList_nil, ← MonoidAlgebra.one_def] using
    wordCoefficients_context ρ [] x

theorem wordCoefficients_right_context (x : WordRing V) (σ : List V) :
    wordCoefficients (x * wordMonomial σ) =
    contextLinear [] σ (wordCoefficients x) := by
  simpa [wordMonomial, FreeMonoid.ofList_nil, ← MonoidAlgebra.one_def] using
    wordCoefficients_context [] σ x

variable [LinearOrder V]

theorem wordRelations_left_mul (y : WordRing V) {x : WordRing V}
    (hx : wordCoefficients x ∈ wordRelations (V := V)) :
    wordCoefficients (y * x) ∈ wordRelations (V := V) := by
  induction y using MonoidAlgebra.induction_on with
  | of m =>
    simpa [← wordCoefficients_left_context, wordMonomial] using
      contextLinear_map_relations (V := V) (FreeMonoid.toList m) [] hx
  | add y z hy hz =>
    simpa only [add_mul, map_add] using (wordRelations (V := V)).add_mem hy hz
  | smul r y hy =>
    simpa only [smul_mul_assoc, map_smul] using (wordRelations (V := V)).smul_mem r hy

theorem wordRelations_right_mul (y : WordRing V) {x : WordRing V}
    (hx : wordCoefficients x ∈ wordRelations (V := V)) :
    wordCoefficients (x * y) ∈ wordRelations (V := V) := by
  induction y using MonoidAlgebra.induction_on with
  | of m =>
    simpa [← wordCoefficients_right_context, wordMonomial] using
      contextLinear_map_relations (V := V) [] (FreeMonoid.toList m) hx
  | add y z hy hz =>
    simpa only [mul_add, map_add] using (wordRelations (V := V)).add_mem hy hz
  | smul r y hy =>
    simpa only [mul_smul_comm, map_smul] using (wordRelations (V := V)).smul_mem r hy

/-! Names oriented by the side on which the arbitrary multiplier occurs. -/

theorem wordCoefficients_mul_mem_left (x y : WordRing V)
    (hy : wordCoefficients y ∈ wordRelations (V := V)) :
    wordCoefficients (x * y) ∈ wordRelations (V := V) :=
  wordRelations_left_mul x hy

theorem wordCoefficients_mul_mem_right (x y : WordRing V)
    (hx : wordCoefficients x ∈ wordRelations (V := V)) :
    wordCoefficients (x * y) ∈ wordRelations (V := V) :=
  wordRelations_right_mul y hx

end

end VerticalStripLLT.Components
