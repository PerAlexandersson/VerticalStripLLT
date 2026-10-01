import VerticalStripLLT.Components.WordProof.BlockListCancellation

/-! Pointwise factorization of the flattened tail indicator. -/

namespace VerticalStripLLT.Components

open Classical

noncomputable section

variable {V : Type*} [LinearOrder V]

private def carrierRel (R : V → V → Prop)
    (B C : Finset V × V) : Prop :=
  ∀ u ∈ B.1, ∀ v ∈ C.1, ¬ R v u

private def zipAssign (X : (Finset V × V) × Finset V) : Finset V × Finset V :=
  (X.1.1, X.2)

private theorem pairwise_zip_assign (R : V → V → Prop)
    (blocks : List (Finset V × V)) (tails : List (Finset V))
    (hlen : tails.length = blocks.length)
    (hcross : blocks.Pairwise (carrierRel R)) :
    ((blocks.zip tails).map zipAssign).Pairwise
      (fun B C => ∀ u ∈ B.1, ∀ v ∈ C.1, ¬ R v u) := by
  have hzip :
      (blocks.zip tails).Pairwise
        (fun X Y => carrierRel R X.1 Y.1) := by
    induction blocks generalizing tails with
    | nil =>
        cases tails <;> simp
    | cons block blocks ih =>
        cases tails with
        | nil => simp at hlen
        | cons tail tails =>
            have hlen' : tails.length = blocks.length := by
              simpa using hlen
            have hc := List.pairwise_cons.mp hcross
            simp only [List.zip_cons_cons]
            apply List.pairwise_cons.mpr
            constructor
            · intro X hX
              exact hc.1 X.1 (List.of_mem_zip hX).1
            · exact ih tails hlen' hc.2
  rw [List.pairwise_map]
  exact hzip

theorem flattenedTailCompatibilityIndicator_cons_factor
    (R : V → V → Prop) (B : Finset V) (r : V)
    (blocks : List (Finset V × V))
    (hcross : ((B, r) :: blocks).Pairwise (carrierRel R))
    (T : Finset V) (hT : T ∈ (B.erase r).powerset)
    (tails : List (Finset V)) :
    flattenedTailCompatibilityIndicator R ((B, r) :: blocks) (T :: tails) =
      (if wordCompatible R (blockWord B T) then 1 else 0) *
        flattenedTailCompatibilityIndicator R blocks tails := by
  by_cases hvalid : tails.length = blocks.length ∧
      ∀ X ∈ blocks.zip tails, X.2 ⊆ X.1.1
  · have hTsub : T ⊆ B := by
      exact (Finset.mem_powerset.mp hT).trans (Finset.erase_subset _ _)
    have hfullvalid :
        (T :: tails).length = ((B, r) :: blocks).length ∧
          ∀ X ∈ ((B, r) :: blocks).zip (T :: tails), X.2 ⊆ X.1.1 := by
      constructor
      · simpa [hvalid.1]
      · intro X hX
        simp only [List.zip_cons_cons] at hX
        rcases List.mem_cons.mp hX with rfl | hX
        · exact hTsub
        · exact hvalid.2 X hX
    have hsub_tail :
        ∀ X ∈ (blocks.zip tails).map zipAssign, X.2 ⊆ X.1 := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
      exact hvalid.2 Y hY
    have hpair_tail := pairwise_zip_assign R blocks tails hvalid.1 (List.pairwise_cons.mp hcross).2
    have hpair_full := pairwise_zip_assign R ((B, r) :: blocks) (T :: tails)
      hfullvalid.1 hcross
    have hzipassign :
        (((B, r) :: blocks).zip (T :: tails)).map zipAssign =
          (B, T) :: (blocks.zip tails).map zipAssign := by
      simp [zipAssign]
    rw [flattenedTailCompatibilityIndicator, dite_eq_left hfullvalid,
      flattenedTailCompatibilityIndicator, dite_eq_left hvalid]
    rw [hzipassign] at hpair_full
    simpa only [List.map_cons, List.zip_cons_cons, List.map_map,
      Function.comp_def, zipAssign] using
      (blockWords_flatten_indicator_cons_eq R (B, T)
        ((blocks.zip tails).map zipAssign) hTsub hsub_tail hpair_full)
  · have hfullinvalid :
        ¬((T :: tails).length = ((B, r) :: blocks).length ∧
          ∀ X ∈ ((B, r) :: blocks).zip (T :: tails), X.2 ⊆ X.1.1) := by
      intro h
      apply hvalid
      constructor
      · simpa using h.1
      · intro X hX
        exact h.2 X (by simp only [List.zip_cons_cons, List.mem_cons]; exact Or.inr hX)
    simp only [flattenedTailCompatibilityIndicator, dite_eq_right hfullinvalid,
      dite_eq_right hvalid, mul_zero]

theorem flattenedTailCompatibilitySum_eq_of_cross
    (R : V → V → Prop) (hinc : ∀ ⦃u v⦄, R u v → u < v)
    (blocks : List (Finset V × V))
    (hroot : ∀ Br ∈ blocks, Br.2 ∈ Br.1 ∧ ∀ u ∈ Br.1, u ≤ Br.2)
    (hcross : blocks.Pairwise (carrierRel R)) :
    flattenedTailCompatibilitySum R blocks =
      if (∀ Br ∈ blocks, ∀ u ∈ Br.1, sinkOn R Br.1 u ↔ u = Br.2) ∧
        blocks.Pairwise (carrierRel R) then 1
      else 0 := by
  have hc : blocks.Pairwise (fun B C => ∀ u ∈ B.1, ∀ v ∈ C.1, ¬ R v u) := hcross
  simpa only [hcross, hc, and_true] using
    flattenedTailCompatibilitySum_eq_of_cross_factor R hinc blocks hroot hcross
      (fun B r blocks' hcross' T hT tails =>
        flattenedTailCompatibilityIndicator_cons_factor R B r blocks' hcross' T hT tails)

end

end VerticalStripLLT.Components
