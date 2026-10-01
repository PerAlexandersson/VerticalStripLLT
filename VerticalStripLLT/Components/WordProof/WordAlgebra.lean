import VerticalStripLLT.Components.WordProof.WordMultiplication
import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-! The word ring quotient, with its exact connection to the additive word quotient. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {V : Type*} [LinearOrder V]

/-- The contextual word relations form a two-sided ideal in the free word ring. -/
def wordIdeal : TwoSidedIdeal (WordRing V) :=
  TwoSidedIdeal.mk' {x | wordCoefficients x ∈ wordRelations (V := V)}
    (by simp)
    (by intro x y hx hy; simpa using (wordRelations (V := V)).add_mem hx hy)
    (by intro x hx; simpa using (wordRelations (V := V)).neg_mem hx)
    (by intro x y hy; exact wordRelations_left_mul x hy)
    (by intro x y hx; exact wordRelations_right_mul y hx)

@[simp]
theorem mem_wordIdeal (x : WordRing V) :
    x ∈ wordIdeal ↔ wordCoefficients x ∈ wordRelations (V := V) := by
  simp [wordIdeal]

/-- The noncommutative ring used by the finite word factorization. -/
abbrev WordAlgebra (V : Type*) [LinearOrder V] :=
  (wordIdeal (V := V)).ringCon.Quotient

/-- Projection of the free ring onto the contextual word algebra. -/
def wordProjection : WordRing V →+* WordAlgebra V :=
  (wordIdeal (V := V)).ringCon.mk'

theorem wordProjection_surjective : Function.Surjective (wordProjection (V := V)) :=
  (wordIdeal (V := V)).ringCon.mk'_surjective

/-- Ring-quotient equality imposes exactly the original additive relations. -/
theorem wordProjection_eq_iff (x y : WordRing V) :
    wordProjection x = wordProjection y ↔
      (wordRelations (V := V)).mkQ (wordCoefficients x) =
        (wordRelations (V := V)).mkQ (wordCoefficients y) := by
  change (x : (wordIdeal (V := V)).ringCon.Quotient) = y ↔ _
  rw [RingCon.eq, TwoSidedIdeal.rel_iff, mem_wordIdeal, map_sub]
  exact (Submodule.Quotient.eq (wordRelations (V := V))).symm

/-- Coefficients of the ring quotient, valued in the original additive quotient. -/
def algebraCoefficients : WordAlgebra V →+ WordQuotient V where
  toFun := Quotient.lift
    (fun x => (wordRelations (V := V)).mkQ (wordCoefficients x))
    (fun x y h => (wordProjection_eq_iff x y).mp (Quotient.sound h))
  map_zero' := by change (wordRelations (V := V)).mkQ (wordCoefficients 0) = 0; simp
  map_add' := by
    intro x y
    obtain ⟨x, rfl⟩ := wordProjection_surjective x
    obtain ⟨y, rfl⟩ := wordProjection_surjective y
    change (wordRelations (V := V)).mkQ (wordCoefficients (x + y)) =
      (wordRelations (V := V)).mkQ (wordCoefficients x) +
        (wordRelations (V := V)).mkQ (wordCoefficients y)
    simp

@[simp]
theorem algebraCoefficients_projection (x : WordRing V) :
    algebraCoefficients (wordProjection x) =
      (wordRelations (V := V)).mkQ (wordCoefficients x) := rfl

theorem algebraCoefficients_bijective :
    Function.Bijective (algebraCoefficients (V := V)) := by
  constructor
  · intro x y h
    obtain ⟨x, rfl⟩ := wordProjection_surjective x
    obtain ⟨y, rfl⟩ := wordProjection_surjective y
    exact (wordProjection_eq_iff x y).mpr h
  · intro x
    obtain ⟨x, rfl⟩ := (wordRelations (V := V)).mkQ_surjective x
    exact ⟨wordProjection (wordCoefficients.symm x), by simp⟩

/-- A component functional remains linear when transported to the word ring quotient. -/
def wordAlgebraEquiv : WordAlgebra V ≃ₗ[ℤ] WordQuotient V :=
  (AddEquiv.ofBijective algebraCoefficients algebraCoefficients_bijective).toIntLinearEquiv

end

end VerticalStripLLT.Components
