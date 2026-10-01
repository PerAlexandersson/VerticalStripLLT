import VerticalStripLLT.Components.WordProof.WordRelations
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! Prefix and suffix maps preserve the additive word relations. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {V : Type*} [LinearOrder V]

def contextMap (ρ σ : List V) : List V → List V :=
  fun w => ρ ++ w ++ σ

/-- The linear map adding a fixed prefix and suffix to every word. -/
def contextLinear (ρ σ : List V) : WordModule V →ₗ[ℤ] WordModule V :=
  Finsupp.lmapDomain ℤ ℤ (contextMap ρ σ)

omit [LinearOrder V] in
@[simp]
theorem contextLinear_basisWord (ρ σ w : List V) :
    contextLinear ρ σ (basisWord w) = basisWord (ρ ++ w ++ σ) := by
  simp [contextLinear, contextMap, basisWord, Finsupp.lmapDomain_apply]

omit [LinearOrder V] in
@[simp]
theorem contextLinear_fourWord (ρ σ τ υ : List V) (a b c : V) :
    contextLinear ρ σ (fourWord τ υ a b c) =
      fourWord (ρ ++ τ) (υ ++ σ) a b c := by
  simp only [fourWord, map_add, map_sub, contextLinear_basisWord]
  simp only [List.append_assoc]

omit [LinearOrder V] in
private theorem nodup_of_context_nodup (ρ σ w : List V)
    (h : (ρ ++ w ++ σ).Nodup) : w.Nodup := by
  have h' : (w ++ σ).Nodup :=
    (List.nodup_append.mp (by simpa only [List.append_assoc] using h)).2.1
  exact (List.nodup_append.mp h').1

theorem contextLinear_relations_comap (ρ σ : List V) :
    wordRelations (V := V) ≤
      (wordRelations (V := V)).comap (contextLinear ρ σ) := by
  change Submodule.span ℤ wordGenerators ≤ _
  refine Submodule.span_le.2 ?_
  intro x hx
  change contextLinear ρ σ x ∈ wordRelations (V := V)
  change (∃ w, ¬w.Nodup ∧ x = basisWord w) ∨
    ∃ τ υ a b c, a < b ∧ b < c ∧ x = fourWord τ υ a b c at hx
  rcases hx with ⟨w, hw, rfl⟩ | ⟨τ, υ, a, b, c, hab, hbc, rfl⟩
  · refine Submodule.subset_span ?_
    refine Or.inl ⟨ρ ++ w ++ σ, ?_, ?_⟩
    · intro hnodup
      exact hw (nodup_of_context_nodup ρ σ w hnodup)
    · rw [contextLinear_basisWord]
  · refine Submodule.subset_span ?_
    refine Or.inr ⟨ρ ++ τ, υ ++ σ, a, b, c, hab, hbc, ?_⟩
    rw [contextLinear_fourWord]

theorem contextLinear_map_relations (ρ σ : List V) {x : WordModule V}
    (hx : x ∈ wordRelations (V := V)) :
    contextLinear ρ σ x ∈ wordRelations (V := V) :=
  contextLinear_relations_comap ρ σ hx

noncomputable def contextQuotient (ρ σ : List V) :
    WordQuotient V →ₗ[ℤ] WordQuotient V :=
  (wordRelations (V := V)).liftQ
    ((wordRelations (V := V)).mkQ.comp (contextLinear ρ σ)) (by
      intro x hx
      change (wordRelations (V := V)).mkQ (contextLinear ρ σ x) = 0
      apply (Submodule.Quotient.mk_eq_zero (wordRelations (V := V))).2
      exact contextLinear_map_relations ρ σ hx)

@[simp]
theorem contextQuotient_mk (ρ σ : List V) (x : WordModule V) :
    contextQuotient ρ σ ((wordRelations (V := V)).mkQ x) =
      (wordRelations (V := V)).mkQ (contextLinear ρ σ x) := by
  rfl

end

end VerticalStripLLT.Components
