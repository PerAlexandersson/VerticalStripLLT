import VerticalStripLLT.Circular.DDResolvedChild

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram.DDLocalData

theorem exists_oneBounce_restart_of_interior_overlap
    {n : ℕ} {D : Diagram n} {t x : ℤ} {k : ℕ}
    (B : D.DDLocalData t) (ht : D.EligibleDE t) (ha : D.edgeData.Admissible ∅)
    (h : ReverseBounceN D t x (k + 1))
    (hx : ¬ D.strictAt x) (hx1 : D.strictAt (x + 1))
    (hinner : ∃ i : ℕ, 1 ≤ i ∧ i ≤ k + 1 ∧
      D.residue (D.boundary^[i] t) = D.residue (x + 1)) :
    ∃ s y : ℤ, B.resolved.EligibleDE s ∧
      ReverseBounceN B.resolved s y 0 ∧ ¬ B.resolved.strictAt (y + 1) := by
  have hn : 2 ≤ n := by
    have := ht.2.1
    have := D.area.bound (D.residue t)
    lia
  obtain ⟨hx, hdd, hgx, -⟩ := (D.reverseBounceN_iff_iterate).mp h
  obtain ⟨i, hi1, hik, hires⟩ := hinner
  subst hx
  -- Propagate the overlap along the main and parallel strict chains.
  have hprop : ∀ l, l ≤ i →
      D.residue (D.boundary^[i - l] t) = D.residue (D.boundary^[k + 2 - l] t + 1) := by
    intro l
    induction l with
    | zero => intro _; simpa using hires
    | succ l ih =>
      intro hl
      have hmain := bounce_main_step ht.1 hdd (i - (l + 1)) (by lia)
      have hpar := bounce_parallel_step hdd (k + 1 - l) (by lia) (by lia)
      rw [show i - (l + 1) + 1 = i - l by lia, ih (by lia)] at hmain
      rw [show k + 1 - l + 1 = k + 2 - l by lia] at hpar
      rw [show k + 2 - (l + 1) = k + 1 - l by lia]
      exact D.strict_selected_rightUnique hmain hpar
  have hqt : D.residue (D.boundary t + 1) ≠ D.residue t := by
    rw [← B.gh, ← B.fh]
    intro hgf
    exact B.hfg (D.strict_edge_eq_of_head_eq B.hf B.hg hgf.symm)
  have hT := hprop i le_rfl
  rw [Nat.sub_self, Function.iterate_zero_apply] at hT
  -- The overlap cannot occur at the last contact row.
  have hik' : i ≤ k := by
    by_contra hcon
    have hi : i = k + 1 := by lia
    rw [hi, show k + 2 - (k + 1) = 1 by lia, Function.iterate_one] at hT
    exact hqt hT.symm
  have hB := hprop (i - 1) (by lia)
  rw [show i - (i - 1) = 1 by lia, Function.iterate_one,
    show k + 2 - (i - 1) = (k + 2 - i) + 1 by lia] at hB
  set j := k + 2 - i with hj
  have hj2 : 2 ≤ j := by lia
  have hjk : j ≤ k + 1 := by lia
  set s := D.boundary^[j] t with hs
  have hys : D.boundary^[j + 1] t = D.boundary s := Function.iterate_succ_apply' _ _ _
  rw [hys] at hB
  set y := D.boundary s with hy
  obtain ⟨hgs, hss, hss1⟩ := hdd j (by lia) hjk
  change D.eastGap s = 0 at hgs
  change D.strictAt s at hss
  change D.strictAt (s + 1) at hss1
  have hs0 :=
    bounce_residue_ne_parallel_end ht hn hdd j (by lia) (by lia)
  have hs1 := bounce_residue_ne_root ht.1 ha hdd j (by lia) (by lia)
  have hs2 := bounce_residue_ne_contact ht.1 ha hdd j hj2 (by lia)
  have hy0 :=
    bounce_residue_ne_parallel_end ht hn hdd (j + 1) (by lia) (by lia)
  have hy1 := bounce_residue_ne_root ht.1 ha hdd (j + 1) (by lia) (by lia)
  have hy2 := bounce_residue_ne_contact ht.1 ha hdd (j + 1) (by lia) (by lia)
  rw [hys] at hy0 hy1 hy2
  change D.residue s ≠ _ at hs0 hs1 hs2
  have hbt : D.residue (D.boundary t) ≠ D.residue t := by
    have := bounce_residue_ne_root ht.1 ha hdd 1 le_rfl (by lia)
    rwa [Function.iterate_one] at this
  -- Boundary data of the resolved diagram at `s`, `s + 1`, `y`, `y + 1`.
  have hbs1 : D.boundary (s + 1) = y + 1 := by
    unfold eastGap at hgs
    rw [ite_eq_left hss] at hgs
    lia
  have hrbs : B.resolved.boundary s = y := B.resolved_boundary_of_ne s hs0 hs1
  have hroot : 2 ≤ D.area.area (D.residue t) := ht.2.1
  have hrbs1 : B.resolved.boundary (s + 1) = y + 2 := by
    have h1 : D.boundary (s + 1) = s + 1 - (D.area.area (D.residue t) : ℤ) := by
      rw [boundary, ← hT]
    rw [boundary, B.resolved_residue, B.resolved_area, ← hT, Function.update_self]
    push_cast [Nat.cast_sub (show 1 ≤ D.area.area (D.residue t) by lia)]
    lia
  have hys1 : y + 1 < s := by
    have hlt := D.strictAt_boundary_lt_self hss1
    rw [hbs1] at hlt
    rcases lt_or_eq_of_le (show y + 1 ≤ s by lia) with h' | h'
    · exact h'
    · exfalso
      apply hs2
      rw [← h', hB]
  have harea_s : 2 ≤ B.resolved.area.area (B.resolved.residue s) := by
    rw [B.resolved_residue, B.resolved_area, Function.update_of_ne hs1,
      Function.update_of_ne hs0]
    have : D.boundary s = s - (D.area.area (D.residue s) : ℤ) := rfl
    lia
  have hrss : B.resolved.strictAt s := (B.resolved_strictAt_iff s).mpr ⟨hss, hs2⟩
  have hny1 : ¬ B.resolved.strictAt (y + 1) := by
    rw [B.resolved_strictAt_iff]
    rintro ⟨-, hne⟩
    exact hne hB.symm
  have hgy : D.eastGap y = 0 := by
    rcases lt_or_eq_of_le (show j + 1 ≤ k + 2 by lia) with h' | h'
    · have := (hdd (j + 1) (by lia) (by lia)).1
      rwa [hys] at this
    · have : D.boundary^[k + 2] t = y := by rw [← h', hys]
      rw [← this]
      exact hgx
  have hrgy : B.resolved.eastGap y = 0 := by
    rw [B.resolved_eastGap_of_ne y hy0 hy1 (by rw [← hB]; exact D.residue_p_ne_succ hn _)
      (by rw [← hB]; exact hbt) hy2]
    exact hgy
  refine ⟨s, y, ⟨hrss, harea_s, ?_⟩, ?_, hny1⟩
  · unfold eastGap
    rw [ite_eq_left hrss, hrbs, hrbs1]
    norm_num
  · rw [ReverseBounceN.zero_iff]
    exact ⟨hrbs.symm, hrgy, fun hc => hny1 hc.2⟩

end VerticalStripLLT.Circular.Diagram.DDLocalData
