import VerticalStripLLT.OrientationConcatSplit

namespace VerticalStripLLT
open scoped BigOperators
open SchroderPath

namespace OrientationConcat

variable {n k : ℕ} (P : SchroderPath n) (R : SchroderPath k)

theorem upwardStep_castAdd_castAdd (θ : Orientation (P.concat R)) (u v : Fin n) :
    upwardStep (P.concat R) θ (Fin.castAdd k u) (Fin.castAdd k v) ↔
      upwardStep P (restrictLeft P R θ) u v := by
  unfold upwardStep
  have hs : (Fin.castAdd k u, Fin.castAdd k v) ∈ (P.concat R).strictEdges ↔
      (u, v) ∈ P.strictEdges := by
    rw [concat_strictEdges, Finset.mem_union, mem_left_map_iff,
      iff_false_intro (not_mem_right_map (by simp)), or_false]
  have hn : (Fin.castAdd k u, Fin.castAdd k v) ∈ (P.concat R).normalEdges ↔
      (u, v) ∈ P.normalEdges := by
    rw [concat_normalEdges, Finset.mem_union, mem_left_map_iff,
      iff_false_intro (not_mem_right_map (by simp)), or_false]
  rw [hs]
  apply or_congr_right
  constructor
  · rintro ⟨h, ht⟩
    exact ⟨hn.1 h, ht⟩
  · rintro ⟨h, ht⟩
    exact ⟨hn.2 h, ht⟩

theorem upwardStep_natAdd_natAdd (θ : Orientation (P.concat R)) (u v : Fin k) :
    upwardStep (P.concat R) θ (Fin.natAdd n u) (Fin.natAdd n v) ↔
      upwardStep R (restrictRight P R θ) u v := by
  unfold upwardStep
  have hs : (Fin.natAdd n u, Fin.natAdd n v) ∈ (P.concat R).strictEdges ↔
      (u, v) ∈ R.strictEdges := by
    rw [concat_strictEdges, Finset.mem_union, mem_right_map_iff,
      iff_false_intro (not_mem_left_map (by simp)), false_or]
  have hn : (Fin.natAdd n u, Fin.natAdd n v) ∈ (P.concat R).normalEdges ↔
      (u, v) ∈ R.normalEdges := by
    rw [concat_normalEdges, Finset.mem_union, mem_right_map_iff,
      iff_false_intro (not_mem_left_map (by simp)), false_or]
  rw [hs]
  apply or_congr_right
  constructor
  · rintro ⟨h, ht⟩
    exact ⟨hn.1 h, ht⟩
  · rintro ⟨h, ht⟩
    exact ⟨hn.2 h, ht⟩

theorem not_upwardStep_castAdd_natAdd (θ : Orientation (P.concat R)) (u : Fin n)
    (v : Fin k) : ¬ upwardStep (P.concat R) θ (Fin.castAdd k u) (Fin.natAdd n v) := by
  rintro (h | ⟨h, _⟩)
  · rw [concat_strictEdges, Finset.mem_union] at h
    rcases h with h | h
    · exact not_mem_left_map (by simp) h
    · exact not_mem_right_map (by simp) h
  · rw [concat_normalEdges, Finset.mem_union] at h
    rcases h with h | h
    · exact not_mem_left_map (by simp) h
    · exact not_mem_right_map (by simp) h

theorem not_upwardStep_natAdd_castAdd (θ : Orientation (P.concat R)) (u : Fin k)
    (v : Fin n) : ¬ upwardStep (P.concat R) θ (Fin.natAdd n u) (Fin.castAdd k v) := by
  intro h
  have h' := upwardStep_lt h
  rw [Fin.lt_def] at h'
  simp only [Fin.val_natAdd, Fin.val_castAdd] at h'
  have := v.isLt
  lia

theorem reachable_castAdd_iff (θ : Orientation (P.concat R)) (u : Fin n)
    (w : Fin (n + k)) :
    reachable θ (Fin.castAdd k u) w ↔
      ∃ v, w = Fin.castAdd k v ∧ reachable (restrictLeft P R θ) u v := by
  constructor
  · intro h
    change Relation.ReflTransGen _ _ _ at h
    induction h with
    | refl => exact ⟨u, rfl, self_reachable _ u⟩
    | @tail b c _ hbc ih =>
        obtain ⟨v, rfl, hv⟩ := ih
        cases c using Fin.addCases with
        | left j =>
            exact ⟨j, rfl, Relation.ReflTransGen.tail hv
              ((upwardStep_castAdd_castAdd P R θ v j).1 hbc)⟩
        | right j => exact absurd hbc (not_upwardStep_castAdd_natAdd P R θ v j)
  · rintro ⟨v, rfl, hv⟩
    exact Relation.ReflTransGen.lift (Fin.castAdd k)
      (fun a b h => (upwardStep_castAdd_castAdd P R θ a b).2 h) u v hv

theorem reachable_natAdd_iff (θ : Orientation (P.concat R)) (u : Fin k)
    (w : Fin (n + k)) :
    reachable θ (Fin.natAdd n u) w ↔
      ∃ v, w = Fin.natAdd n v ∧ reachable (restrictRight P R θ) u v := by
  constructor
  · intro h
    change Relation.ReflTransGen _ _ _ at h
    induction h with
    | refl => exact ⟨u, rfl, self_reachable _ u⟩
    | @tail b c _ hbc ih =>
        obtain ⟨v, rfl, hv⟩ := ih
        cases c using Fin.addCases with
        | left j => exact absurd hbc (not_upwardStep_natAdd_castAdd P R θ v j)
        | right j =>
            exact ⟨j, rfl, Relation.ReflTransGen.tail hv
              ((upwardStep_natAdd_natAdd P R θ v j).1 hbc)⟩
  · rintro ⟨v, rfl, hv⟩
    exact Relation.ReflTransGen.lift (Fin.natAdd n)
      (fun a b h => (upwardStep_natAdd_natAdd P R θ a b).2 h) u v hv

/-! ### Highest reachable vertices -/

theorem hrv_castAdd (θ : Orientation (P.concat R)) (u : Fin n) :
    hrv θ (Fin.castAdd k u) = Fin.castAdd k (hrv (restrictLeft P R θ) u) := by
  apply le_antisymm
  · obtain ⟨v, hv, hr⟩ := (reachable_castAdd_iff P R θ u _).1 (reachable_hrv θ _)
    rw [hv]
    have h := reachable_le_hrv _ u v hr
    rw [Fin.le_def] at h ⊢
    simpa using h
  · exact reachable_le_hrv θ _ _
      ((reachable_castAdd_iff P R θ u _).2 ⟨_, rfl, reachable_hrv _ u⟩)

theorem hrv_natAdd (θ : Orientation (P.concat R)) (u : Fin k) :
    hrv θ (Fin.natAdd n u) = Fin.natAdd n (hrv (restrictRight P R θ) u) := by
  apply le_antisymm
  · obtain ⟨v, hv, hr⟩ := (reachable_natAdd_iff P R θ u _).1 (reachable_hrv θ _)
    rw [hv]
    have h := reachable_le_hrv _ u v hr
    rw [Fin.le_def] at h ⊢
    simpa using h
  · exact reachable_le_hrv θ _ _
      ((reachable_natAdd_iff P R θ u _).2 ⟨_, rfl, reachable_hrv _ u⟩)

/-! ### HRV fibers and monomials -/

theorem natAdd_ne_castAdd (i : Fin k) (j : Fin n) :
    Fin.natAdd n i ≠ Fin.castAdd k j := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at h'
  have := j.isLt
  lia

theorem card_hrvFiber_castAdd (θ : Orientation (P.concat R)) (r : Fin n) :
    (hrvFiber θ (Fin.castAdd k r)).card = (hrvFiber (restrictLeft P R θ) r).card := by
  simp only [hrvFiber, Finset.card_filter]
  rw [Fin.sum_univ_add]
  simp [hrv_castAdd, hrv_natAdd, natAdd_ne_castAdd]

theorem card_hrvFiber_natAdd (θ : Orientation (P.concat R)) (r : Fin k) :
    (hrvFiber θ (Fin.natAdd n r)).card = (hrvFiber (restrictRight P R θ) r).card := by
  simp only [hrvFiber, Finset.card_filter]
  rw [Fin.sum_univ_add]
  simp [hrv_castAdd, hrv_natAdd, (natAdd_ne_castAdd _ _).symm]

omit P R in
theorem fiberFactor_congr {α β : Type*} {s : Finset α} {t : Finset β}
    (h : s.card = t.card) :
    (if hs : s.Nonempty then elementary ⟨s.card, Finset.card_pos.mpr hs⟩ else 1) =
      (if ht : t.Nonempty then elementary ⟨t.card, Finset.card_pos.mpr ht⟩ else 1) := by
  by_cases hs : s.Nonempty
  · have ht : t.Nonempty := Finset.card_pos.mp (h ▸ Finset.card_pos.mpr hs)
    rw [dite_eq_left hs, dite_eq_left ht]
    congr 2
  · have ht : ¬ t.Nonempty := fun ht =>
      hs (Finset.card_pos.mp (h.symm ▸ Finset.card_pos.mpr ht))
    rw [dite_eq_right hs, dite_eq_right ht]

theorem hrvMonomial_concat (θ : Orientation (P.concat R)) :
    hrvMonomial θ = hrvMonomial (restrictLeft P R θ) * hrvMonomial (restrictRight P R θ) := by
  unfold hrvMonomial
  rw [Fin.prod_univ_add]
  congr 1
  · exact Finset.prod_congr rfl fun r _ => fiberFactor_congr (card_hrvFiber_castAdd P R θ r)
  · exact Finset.prod_congr rfl fun r _ => fiberFactor_congr (card_hrvFiber_natAdd P R θ r)

end OrientationConcat
end VerticalStripLLT
