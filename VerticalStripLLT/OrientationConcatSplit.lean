import VerticalStripLLT.ColoringConcat
import VerticalStripLLT.OrientationExpansion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace VerticalStripLLT
open scoped BigOperators
open SchroderPath

namespace OrientationConcat

variable {n k : ℕ} (P : SchroderPath n) (R : SchroderPath k)

/-! ### Splitting the normal edges and the orientations -/

theorem left_mem_concat_normalEdges (a : {e // e ∈ P.normalEdges}) :
    leftPairEmb n k a.1 ∈ (P.concat R).normalEdges := by
  rw [concat_normalEdges]
  exact Finset.mem_union_left _ (Finset.mem_map_of_mem _ a.2)

theorem right_mem_concat_normalEdges (b : {e // e ∈ R.normalEdges}) :
    rightPairEmb n k b.1 ∈ (P.concat R).normalEdges := by
  rw [concat_normalEdges]
  exact Finset.mem_union_right _ (Finset.mem_map_of_mem _ b.2)

theorem leftPairEmb_ne_rightPairEmb (p : Fin n × Fin n) (q : Fin k × Fin k) :
    leftPairEmb n k p ≠ rightPairEmb n k q := by
  intro h
  have h' := congrArg (fun e => e.1.val) h
  simp only [leftPairEmb_apply, rightPairEmb_apply, Fin.val_castAdd, Fin.val_natAdd] at h'
  have := p.1.isLt
  lia

/-- Inclusion of the disjoint union of the block edge subtypes into the
normal edge subtype of the concatenation. -/
def edgeInclusion :
    {e // e ∈ P.normalEdges} ⊕ {e // e ∈ R.normalEdges} →
      {e // e ∈ (P.concat R).normalEdges}
  | Sum.inl a => ⟨leftPairEmb n k a.1, left_mem_concat_normalEdges P R a⟩
  | Sum.inr b => ⟨rightPairEmb n k b.1, right_mem_concat_normalEdges P R b⟩

theorem edgeInclusion_bijective : Function.Bijective (edgeInclusion P R) := by
  constructor
  · rintro (a | b) (a' | b') h <;> simp only [edgeInclusion, Subtype.mk.injEq] at h
    · exact congrArg Sum.inl (Subtype.ext ((leftPairEmb n k).injective h))
    · exact absurd h (leftPairEmb_ne_rightPairEmb a.1 b'.1)
    · exact absurd h.symm (leftPairEmb_ne_rightPairEmb a'.1 b.1)
    · exact congrArg Sum.inr (Subtype.ext ((rightPairEmb n k).injective h))
  · rintro ⟨e, he⟩
    have he' := he
    rw [concat_normalEdges, Finset.mem_union] at he'
    rcases he' with h | h
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 h
      exact ⟨Sum.inl ⟨a, ha⟩, rfl⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 h
      exact ⟨Sum.inr ⟨b, hb⟩, rfl⟩

/-- Normal edges of `P.concat R` are the disjoint union of those of `P` and `R`. -/
noncomputable def edgeEquiv :
    {e // e ∈ P.normalEdges} ⊕ {e // e ∈ R.normalEdges} ≃
      {e // e ∈ (P.concat R).normalEdges} :=
  Equiv.ofBijective _ (edgeInclusion_bijective P R)

theorem card_normalEdges_concat :
    (P.concat R).normalEdges.card = P.normalEdges.card + R.normalEdges.card := by
  have h := Fintype.card_congr (edgeEquiv P R)
  simpa [Fintype.card_sum] using h.symm

/-- Restriction of an orientation of the concatenation to the left block. -/
def restrictLeft (θ : Orientation (P.concat R)) : Orientation P :=
  fun a => θ (edgeInclusion P R (Sum.inl a))

/-- Restriction of an orientation of the concatenation to the right block. -/
def restrictRight (θ : Orientation (P.concat R)) : Orientation R :=
  fun b => θ (edgeInclusion P R (Sum.inr b))

/-- Orientations of `P.concat R` are pairs of orientations of `P` and `R`. -/
noncomputable def orientationSplit :
    Orientation (P.concat R) ≃ Orientation P × Orientation R :=
  ((edgeEquiv P R).arrowCongr (Equiv.refl Bool)).symm.trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

theorem orientationSplit_apply (θ : Orientation (P.concat R)) :
    orientationSplit P R θ = (restrictLeft P R θ, restrictRight P R θ) := rfl

/-! ### Ascents -/

theorem orientationAsc_concat (θ : Orientation (P.concat R)) :
    orientationAsc (P.concat R) θ =
      orientationAsc P (restrictLeft P R θ) + orientationAsc R (restrictRight P R θ) := by
  unfold orientationAsc
  simp only [Finset.card_filter]
  rw [← Fintype.sum_equiv (edgeEquiv P R)
    (fun s => if θ (edgeInclusion P R s) = true then 1 else 0)
    (fun e => if θ e = true then 1 else 0) (fun _ => rfl), Fintype.sum_sum_type]
  rfl

/-! ### Upward steps and reachability -/

end OrientationConcat
end VerticalStripLLT
