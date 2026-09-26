import VerticalStripLLT.Circular.BounceIterates
import VerticalStripLLT.Circular.DDResolvedTransport

namespace VerticalStripLLT.Circular.Diagram.DDLocalData

theorem resolved_dd_child {n : ℕ} {D : Diagram n} {t x : ℤ} {k : ℕ}
    (B : D.DDLocalData t) (ht : D.EligibleDE t) (ha : D.edgeData.Admissible ∅)
    (h : ReverseBounceN D t x (k + 1)) (hx1 : ¬ D.strictAt (x + 1)) :
    B.resolved.EligibleDE (D.boundary t + 1) ∧
      ReverseBounceN B.resolved (D.boundary t + 1) x k ∧
      (B.resolved.strictAt x ↔ D.strictAt x) ∧
      (B.resolved.strictAt (x + 1) ↔ D.strictAt (x + 1)) ∧
      B.resolved.edgeData.Admissible ∅ := by
  have hn : 2 ≤ n := by
    have := ht.2.1
    have := D.area.bound (D.residue t)
    lia
  obtain ⟨hx, hdd, hgx, hnx⟩ := (D.reverseBounceN_iff_iterate).mp h
  subst hx
  have hx1' : ¬ D.strictAt (D.boundary^[k + 2] t + 1) := hx1
  -- Transport of all local data at a visited contact row.
  have transfer : ∀ l, 2 ≤ l → l ≤ k + 2 →
      B.resolved.boundary (D.boundary^[l] t) = D.boundary (D.boundary^[l] t) ∧
      (B.resolved.strictAt (D.boundary^[l] t) ↔ D.strictAt (D.boundary^[l] t)) ∧
      (B.resolved.strictAt (D.boundary^[l] t + 1) ↔ D.strictAt (D.boundary^[l] t + 1)) ∧
      B.resolved.eastGap (D.boundary^[l] t) = D.eastGap (D.boundary^[l] t) := by
    intro l hl2 hl
    have h₀ := bounce_residue_ne_parallel_end ht hn hdd l (by lia) hl
    have h₁ := bounce_residue_ne_root ht.1 ha hdd l (by lia) hl
    have h₂ := bounce_succ_residue_ne_parallel_end ht.1 ha hdd l hl2 hl
    have h₃ := bounce_succ_residue_ne_main ht.1 hdd hx1' l 0 hl2 hl (by lia)
    have h₄ := bounce_residue_ne_contact ht.1 ha hdd l hl2 hl
    have h₅ := bounce_succ_residue_ne_main ht.1 hdd hx1' l 1 hl2 hl le_rfl
    refine ⟨B.resolved_boundary_of_ne _ h₀ h₁, ?_, ?_,
      B.resolved_eastGap_of_ne _ h₀ h₁ h₂ h₃ h₄⟩
    · rw [B.resolved_strictAt_iff]
      exact and_iff_left h₄
    · rw [B.resolved_strictAt_iff]
      exact and_iff_left h₅
  -- The resolved search from the parallel row follows the same contacts.
  have iter : ∀ i, i ≤ k →
      B.resolved.boundary^[i + 1] (D.boundary t + 1) = D.boundary^[i + 2] t := by
    intro i
    induction i with
    | zero => intro _; exact B.resolved_boundary_rows.1
    | succ i ih =>
      intro hi
      rw [Function.iterate_succ_apply', ih (by lia), (transfer (i + 2) le_add_self
        (by lia)).1, ← Function.iterate_succ_apply' D.boundary]
  have hc := (hdd 1 le_rfl (by lia))
  obtain ⟨hgp, hsp, hsq⟩ := hc
  change D.eastGap (D.boundary t) = 0 at hgp
  change D.strictAt (D.boundary t) at hsp
  change D.strictAt (D.boundary t + 1) at hsq
  have hpq : D.residue (D.boundary t + 1) ≠ D.residue (D.boundary t) :=
    (D.residue_p_ne_succ hn _).symm
  have hqt : D.residue (D.boundary t + 1) ≠ D.residue t := by
    rw [← B.gh, ← B.fh]
    intro hgf
    exact B.hfg (D.strict_edge_eq_of_head_eq B.hf B.hg hgf.symm)
  have hsqR : B.resolved.strictAt (D.boundary t + 1) :=
    (B.resolved_strictAt_iff _).mpr ⟨hsq, hpq⟩
  refine ⟨⟨hsqR, ?_, ?_⟩, ?_, ?_, ?_, B.resolved_admissible ht ha⟩
  · -- the raised parallel row has area at least two
    rw [B.resolved_residue, B.resolved_area, Function.update_of_ne hqt, Function.update_self]
    have := D.strictAt_area_pos hsp
    lia
  · -- the resolved parallel row has an east gap
    have hstep : D.boundary (D.boundary t + 1) = D.boundary (D.boundary t) + 1 := by
      unfold eastGap at hgp
      rw [ite_eq_left hsp] at hgp
      lia
    have hlt := D.strictAt_boundary_lt hsq
    have hge := B.resolved_boundary_ge (D.boundary t + 1 + 1)
      (D.residue_p_ne_succ hn _).symm
    have hrow := B.resolved_boundary_rows.1
    unfold eastGap
    rw [ite_eq_left hsqR]
    lia
  · -- the counted search
    apply (B.resolved.reverseBounceN_iff_iterate).mpr
    refine ⟨(iter k le_rfl).symm, ?_, ?_, ?_⟩
    · intro i hi1 hi
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by lia⟩
      rw [iter i' (by lia)]
      obtain ⟨-, hs0, hs1, hg0⟩ := transfer (i' + 2) le_add_self (by lia)
      obtain ⟨hg, h1, h2⟩ := hdd (i' + 2) (by lia) (by lia)
      exact ⟨hg0.trans hg, hs0.mpr h1, hs1.mpr h2⟩
    · rw [(transfer (k + 2) le_add_self le_rfl).2.2.2]
      exact hgx
    · rw [(transfer (k + 2) le_add_self le_rfl).2.1,
        (transfer (k + 2) le_add_self le_rfl).2.2.1]
      exact hnx
  · exact (transfer (k + 2) le_add_self le_rfl).2.1
  · exact (transfer (k + 2) le_add_self le_rfl).2.2.1

end VerticalStripLLT.Circular.Diagram.DDLocalData

