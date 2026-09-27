import VerticalStripLLT.Components.WordAlgebra
import VerticalStripLLT.Components.WordConjugation

/-! The concrete generators satisfy the hypotheses of finite word conjugation. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {V : Type*} [LinearOrder V]

/-- The image of a word in the contextual word algebra. -/
def algebraWord (w : List V) : WordAlgebra V := wordProjection (wordMonomial w)

@[simp]
theorem algebraWord_append (w v : List V) :
    algebraWord (w ++ v) = algebraWord w * algebraWord v := by
  simp [algebraWord, wordMonomial, ← map_mul, MonoidAlgebra.single_mul_single,
    FreeMonoid.ofList_append]

theorem algebraWord_repeated (w : List V) (hw : ¬w.Nodup) : algebraWord w = 0 := by
  change wordProjection (wordMonomial w) = 0
  rw [← map_zero wordProjection, wordProjection_eq_iff]
  simp only [wordCoefficients_wordMonomial, map_zero]
  apply (Submodule.Quotient.mk_eq_zero (wordRelations (V := V))).mpr
  exact Submodule.subset_span (Or.inl ⟨w, hw, rfl⟩)

/-- Repeated letters vanish even with an arbitrary algebra element between them. -/
theorem algebraWord_sandwich (a : V) (Y : WordAlgebra V) :
    algebraWord [a] * Y * algebraWord [a] = 0 := by
  obtain ⟨y, rfl⟩ := wordProjection_surjective Y
  induction y using MonoidAlgebra.induction_on with
  | of w =>
    change algebraWord [a] * algebraWord (FreeMonoid.toList w) * algebraWord [a] = 0
    rw [← algebraWord_append, ← algebraWord_append]
    apply algebraWord_repeated
    simp
  | add x y hx hy => simp only [map_add, mul_add, add_mul, hx, hy, add_zero]
  | smul r x hx => simp only [map_zsmul, mul_smul_comm, smul_mul_assoc, hx, smul_zero]

theorem algebraWord_four (a b c : V) (hab : a < b) (hbc : b < c) :
    algebraWord [a, c, b] + algebraWord [b, c, a] -
      algebraWord [c, a, b] - algebraWord [b, a, c] = 0 := by
  have h : (wordRelations (V := V)).mkQ (fourWord [] [] a b c) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero (wordRelations (V := V))).mpr
    exact Submodule.subset_span (Or.inr ⟨[], [], a, b, c, hab, hbc, rfl⟩)
  apply algebraCoefficients_bijective.injective
  simpa [algebraWord, fourWord, map_add, map_sub] using h

/-- The ordered triple relation in the exact form used by conjugation. -/
theorem algebraWord_triple (a b c : V) (hab : a < b) (hbc : b < c) :
    algebraWord [b] * (algebraWord [a] * algebraWord [c] -
        algebraWord [c] * algebraWord [a]) -
      (algebraWord [a] * algebraWord [c] - algebraWord [c] * algebraWord [a]) *
        algebraWord [b] = 0 := by
  have h := algebraWord_four a b c hab hbc
  have hwords (x y z : V) :
      algebraWord [x, y, z] = algebraWord [x] * algebraWord [y] * algebraWord [z] := by
    rw [← algebraWord_append, ← algebraWord_append]
    rfl
  simp only [hwords] at h
  calc
    _ = -(algebraWord [a] * algebraWord [c] * algebraWord [b] +
        algebraWord [b] * algebraWord [c] * algebraWord [a] -
        algebraWord [c] * algebraWord [a] * algebraWord [b] -
        algebraWord [b] * algebraWord [a] * algebraWord [c]) := by noncomm_ring
    _ = 0 := by rw [h, neg_zero]

end

end VerticalStripLLT.Components
