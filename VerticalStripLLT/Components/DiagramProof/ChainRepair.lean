import VerticalStripLLT.Components.DiagramProof.IntervalPaths
import VerticalStripLLT.Components.DiagramProof.ChildMerge

/-! Repair the missing edge `12` by the four child-merging flips inside `0,1,2,3`. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

/-- Opening above `3` permits the four-flip repair even when `12` is missing.
The two endpoint states differ exactly by replacing `13` with `12`. -/
theorem complete_chain_repair {n : ℕ}
    (θ η : Orientation (completeDiagram n)) (i j t : Fin (n + 1))
    (hi : i.val = 1) (hj : j.val = 2) (ht : t.val = 3)
    (hrow : ∀ v, (completeDiagram n).edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hchain : ∀ u v : Fin (n + 1), t ≤ u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected θ.val u v)
    (h13 : (completeDiagram n).edgeData.selected θ.val i t)
    (h23 : (completeDiagram n).edgeData.selected θ.val j t)
    (h12 : ¬ (completeDiagram n).edgeData.selected θ.val i j)
    (hη : ∀ u v, (completeDiagram n).edgeData.selected η.val u v ↔
      (u = i ∧ v = j) ∨
        ((completeDiagram n).edgeData.selected θ.val u v ∧ ¬ (u = i ∧ v = t))) :
    Relation.ReflTransGen (Flip (completeDiagram n)) θ η := by
  have hn : 1 + 2 ≤ n := by have := t.isLt; lia
  let ι := intervalEmbed 1 2 (by decide) hn
  have hιi : ι (1 : Fin 4) = i := Fin.ext (by change 1 = i.val; lia)
  have hιj : ι (2 : Fin 4) = j := Fin.ext (by change 2 = j.val; lia)
  have hιt : ι (3 : Fin 4) = t := Fin.ext (by change 3 = t.val; lia)
  have hi0 : i ≠ 0 := by intro h; have := congrArg Fin.val h; change i.val = 0 at this; lia
  have hit : i < t := by change i.val < t.val; lia
  have hjt : j < t := by change j.val < t.val; lia
  have htpos : 0 < t := by change 0 < t.val; lia
  have hrowη : ∀ v, (completeDiagram n).edgeData.selected η.val 0 v ↔ v = Fin.last n := by
    intro v
    rw [hη]
    simp [hi0.symm, hrow]
  have hchainη : ∀ u v : Fin (n + 1), t ≤ u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected η.val u v := by
    intro u v htu huv
    apply (hη u v).mpr
    exact Or.inr ⟨hchain u v htu huv, fun h => (not_le_of_gt hit) (h.1 ▸ htu)⟩
  apply complete_interval_chain_path_of_chain_above (a := 1) (m := 2) (by decide) hn
    θ η hrow hrowη
    (fun u v hu huv => hchain u v (hιt ▸ hu) huv)
    (fun u v hu huv => hchainη u v (hιt ▸ hu) huv) ?_ ?_
  · intro u v hout
    rw [hη]
    have hnew : ¬ (u = i ∧ v = j) := by
      rintro ⟨rfl, rfl⟩
      exact hout ⟨1, 2, hιi, hιj⟩
    have hold : ¬ (u = i ∧ v = t) := by
      rintro ⟨rfl, rfl⟩
      exact hout ⟨1, 3, hιi, hιt⟩
    simp [hnew, hold]
  · let α := completeRestrictAlong ι (openCompleteChain θ t htpos)
    let β := completeRestrictAlong ι (openCompleteChain η t htpos)
    have hαrow : ∀ v, (completeDiagram 3).edgeData.selected α.val 0 v ↔ v = Fin.last 3 := by
      intro v
      change (completeDiagram 3).edgeData.selected
        (completeRestrictAlong ι (openCompleteChain θ t htpos)).val 0 v ↔ _
      rw [completeRestrictAlong_selected, intervalEmbed_zero,
        openCompleteChain_row _ _ _ hrow, ← hιt]
      rw [ι.le_iff_le]
      exact ⟨fun h => le_antisymm (Fin.le_last v) h, fun h => h ▸ le_rfl⟩
    have hαi (v : Fin 4) : (completeDiagram 3).edgeData.selected α.val 1 v ↔
        (completeDiagram n).edgeData.selected θ.val i (ι v) := by
      rw [completeRestrictAlong_selected, hιi, openCompleteChain_below θ t htpos i (ι v)]
      · exact Fin.pos_iff_ne_zero.mpr hi0
      · exact hit
    have hαj (v : Fin 4) : (completeDiagram 3).edgeData.selected α.val 2 v ↔
        (completeDiagram n).edgeData.selected θ.val j (ι v) := by
      rw [completeRestrictAlong_selected, hιj, openCompleteChain_below θ t htpos j (ι v)]
      · change 0 < j.val; lia
      · exact hjt
    have hrow1 : ∀ v, (completeDiagram 3).edgeData.selected α.val 1 v ↔ v = 3 := by
      intro v
      constructor
      · intro hs
        have hv := α.selected_lt_of_forward (complete_forward 3) hs
        by_contra hne
        have hv3 : v.val ≠ 3 := fun h => hne (Fin.ext h)
        have hv2 : v = 2 := Fin.ext (by have := v.isLt; change 1 < v.val at hv; lia)
        subst v
        exact h12 (by simpa [hιj] using (hαi 2).mp hs)
      · rintro rfl
        exact (hαi 3).mpr (by simpa [hιt] using h13)
    have hrow2 : ∀ v, (completeDiagram 3).edgeData.selected α.val 2 v ↔ v = 3 := by
      intro v
      constructor
      · intro hs
        have hv := α.selected_lt_of_forward (complete_forward 3) hs
        apply Fin.ext
        have := v.isLt
        change 2 < v.val at hv
        lia
      · rintro rfl
        exact (hαj 3).mpr (by simpa [hιt] using h23)
    obtain ⟨δ, hp, hδ⟩ := exists_childMerge (complete_forward 3) α 0 1 2 3
      (by decide) (by decide) (by decide) hαrow hrow1 hrow2
    have hδβ : δ = β := by
      apply fullSelection_injective
      ext e
      rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected, hδ]
      change _ ↔ (completeDiagram 3).edgeData.selected
        (completeRestrictAlong ι (openCompleteChain η t htpos)).val e.tail e.head
      simp only [completeRestrictAlong_selected, openCompleteChain_selected, hη]
      have hα (x y : Fin 4) : (completeDiagram 3).edgeData.selected α.val x y ↔
          (ι x = 0 ∧ t ≤ ι y) ∨
            ((completeDiagram n).edgeData.selected θ.val (ι x) (ι y) ∧
              ¬ (t ≤ ι x ∧ (ι x).val + 1 = (ι y).val)) := by
        rw [completeRestrictAlong_selected, openCompleteChain_selected]
      rw [hα]
      have he0 : ι e.tail = 0 ↔ e.tail = 0 := by
        change ι e.tail = ι 0 ↔ _
        exact ι.injective.eq_iff
      have hei : ι e.tail = i ↔ e.tail = 1 := by rw [← hιi, ι.injective.eq_iff]
      have hej : ι e.head = j ↔ e.head = 2 := by rw [← hιj, ι.injective.eq_iff]
      have het : ι e.head = t ↔ e.head = 3 := by rw [← hιt, ι.injective.eq_iff]
      have hbelow : e.tail = 1 → ¬ t ≤ ι e.tail := by
        rintro h
        rw [h, hιi]
        exact not_le_of_gt hit
      rw [he0, hei, hej, het]
      clear hη hδ hchain hchainη hrow hrowη hαrow hrow1 hrow2 hαi hαj hα hp
      grind only
    rw [hδβ] at hp
    change Relation.ReflTransGen (Flip (completeDiagram 3))
      (completeRestrictAlong ι (openCompleteChain θ (ι 3) _))
      (completeRestrictAlong ι (openCompleteChain η (ι 3) _))
    simpa only [hιt] using hp

end VerticalStripLLT.Circular.DiagramProof
