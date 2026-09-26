import VerticalStripLLT.Circular.DNReductionDiamond
import VerticalStripLLT.Circular.DDResolvedChild
import VerticalStripLLT.Circular.DDDeletedChild
import VerticalStripLLT.Circular.DDLocalRealization
import VerticalStripLLT.Circular.DDRecurrences
import VerticalStripLLT.QShiftInjective

set_option backward.isDefEq.respectTransparency false

/-! Full DN by induction on the number of DD contacts of the reverse bounce. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ}

/-- The inductive claim with `k` DD contacts: both models agree on the source and on any
diagram with the rows of its DN target (coloring after the shift `q ↦ q + 1`). -/
def DNModelsClaim (n k : ℕ) : Prop :=
  ∀ (D : Diagram n) (t x : ℤ), D.edgeData.Admissible ∅ → D.EligibleDE t →
    ReverseBounceN D t x k → D.strictAt x → ¬ D.strictAt (x + 1) →
      ∀ T : Diagram n, IsDNTarget D t x T →
        (∀ m : ℕ, xQShift m (D.coloringLLT m) = xQShift m (T.coloringLLT m)) ∧
          shiftedOrientationExpansion D = shiftedOrientationExpansion T

/-- No DD contact: the DN target is the actual one-bounce DN successor. -/
theorem dnModelsClaim_zero : DNModelsClaim n 0 := by
  intro D t x ha ht h hx hx1 T hT
  obtain ⟨e, f, he, hf, hfe, heq, hb, hns, hlen, hgap, eh, fh, -⟩ :=
    D.exists_dn_data ha ht h.to_reverseBounce hx hx1
  have hTS := hT.eq (D.dnSuccessor_isDNTarget e f he hf hfe heq hb hns hlen hgap eh fh)
  subst hTS
  have hx0 : x = D.boundary t := ((ReverseBounceN.zero_iff D).mp h).1
  have hcontact : f.tail = e.head := by
    rw [D.strictEdge_tail_of_lift hf fh, eh, hx0]
  exact ⟨fun m => by
      rw [D.coloringLLT_dnSuccessor e f he hf hfe hcontact heq hb hns hlen hgap m],
    D.shiftedOrientationExpansion_dnSuccessor e f he hf hfe hcontact heq hb hns hlen hgap⟩

/-- One more DD contact: resolve the last DD contact, apply the claim to both children,
and close the diamond with the unstrict-corner relation of the source target. -/
theorem dnModelsClaim_succ {k : ℕ} (ih : DNModelsClaim n k) : DNModelsClaim n (k + 1) := by
  intro D t x ha ht h hx hx1 T hT
  obtain ⟨B⟩ := D.exists_ddLocalData ht h
  obtain ⟨-, hc, -, child⟩ := D.reverseBounceN_succ_iff.mp h
  obtain ⟨hRt, hRk, hRx, hRx1, hRa⟩ := B.resolved_dd_child ht ha h hx1
  obtain ⟨hEt, hEk, hEx, hEx1, hEa⟩ := D.delete_dd_child ht ha h B.g B.hg B.gh
  -- residue separation of the terminal, root, contact and parallel rows
  have hpath := child.selected_path D hc
  obtain ⟨hdb, hab⟩ := ht.terminal_rows_ne D ha hpath
  have hdP : D.residue x ≠ D.residue (D.boundary t) := by
    intro hh
    rw [hh] at hpath
    exact ha _ hpath
  have hdc : D.residue x ≠ D.residue t := by
    intro hh
    have hp := h.selected_path D ht.1
    rw [hh] at hp
    exact ha _ hp
  have hac : D.residue (x + 1) ≠ D.residue t := (D.residue_ne_of_strictAt ht.1 hx1).symm
  have haP : D.residue (x + 1) ≠ D.residue (D.boundary t) :=
    (D.residue_ne_of_strictAt hc hx1).symm
  -- the old last-contact row is still strict in the source target
  obtain ⟨c, hcT, cH⟩ : T.strictAt (D.boundary t) := (hT.2 _).mpr (Or.inl ⟨hc, hdP.symm⟩)
  rw [residue_congr T D] at cH
  -- resolved child
  have hU := B.unstrict_isDNTarget hT c hcT cH hab hac hdb hdc haP
  obtain ⟨ihRc, ihRo⟩ := ih B.resolved (D.boundary t + 1) x hRa hRt hRk (hRx.mpr hx)
    (fun h' => hx1 (hRx1.mp h')) _ hU
  -- deleted child
  have hEx' : B.deleted.strictAt x := hEx.mpr hx
  have hEx1' : ¬ B.deleted.strictAt (x + 1) := fun h' => hx1 (hEx1.mp h')
  obtain ⟨e1, f1, he1, hf1, hfe1, heq1, hb1, hns1, hlen1, hgap1, e1h, f1h, -⟩ :=
    B.deleted.exists_dn_data hEa hEt hEk.to_reverseBounce hEx' hEx1'
  have hV := B.deleted.dnSuccessor_isDNTarget e1 f1 he1 hf1 hfe1 heq1 hb1 hns1 hlen1 hgap1
    e1h f1h
  obtain ⟨ihEc, ihEo⟩ := ih B.deleted (D.boundary t) x hEa hEt hEk hEx' hEx1' _ hV
  obtain ⟨hVWc, hVWo⟩ := B.deleted_target_models hT c hcT cH hV ht hc hab hac hdb hdc haP hdP
  refine ⟨fun m => ?_, ?_⟩
  · apply mul_left_cancel₀ (C_X_ne_zero_xPoly m)
    rw [B.coloring_resolution m, ihRc m, ihEc m, hVWc m,
      T.xQShift_coloringLLT_unstrict_corner c hcT m]
    ring
  · apply mul_left_cancel₀ C_X_ne_zero_eExpansion
    rw [B.orientation_resolution, ihRo, ihEo, hVWo,
      T.shiftedOrientationExpansion_unstrict_corner c hcT]
    ring

theorem dnModelsClaim_all (n k : ℕ) : DNModelsClaim n k := by
  induction k with
  | zero => exact dnModelsClaim_zero
  | succ k ih => exact dnModelsClaim_succ ih

end VerticalStripLLT.Circular.Diagram


namespace VerticalStripLLT.Circular.Diagram

/-- The actual DN reduction, obtained by eliminating DD contacts with local relations. -/
theorem exists_dn_reduction {n : ℕ} (D : Diagram n) {t x : ℤ}
    (ha : D.edgeData.Admissible ∅) (ht : D.EligibleDE t)
    (h : ReverseBounce D t x) (hx : D.strictAt x) (hx1 : ¬ D.strictAt (x + 1)) :
    ∃ D' : Diagram n,
      D'.edgeData.Admissible ∅ ∧ D'.doubledArea = D.doubledArea ∧
      D'.strictRank < D.strictRank ∧
      (∀ m : ℕ, D.coloringLLT m = D'.coloringLLT m) ∧
      shiftedOrientationExpansion D = shiftedOrientationExpansion D' := by
  obtain ⟨k, hk⟩ := (reverseBounce_iff_counted D).mp h
  obtain ⟨e, f, he, hf, hfe, heq, hb, hns, hlen, hgap, eh, fh, ⟨C⟩⟩ :=
    D.exists_dn_data ha ht h hx hx1
  have hT := D.dnSuccessor_isDNTarget e f he hf hfe heq hb hns hlen hgap eh fh
  obtain ⟨hcol, hor⟩ :=
    dnModelsClaim_all n k D t x ha ht hk hx hx1 _ hT
  have hfirst : D.area.area (D.residue (x + 1)) = D.area.area (D.residue x) := by
    rw [D.residue_succ]
    exact D.strict_zero_gap_area_eq hx h.terminal_gap.1
  have hsum :=
    D.area_sum_eq_of_two_row_update _ (D.residue (x + 1)) (D.residue t)
    (D.residue_ne_of_strictAt ht.1 hx1).symm (by have := ht.2.1; lia)
    (by rw [hfirst]; exact hT.1)
  exact ⟨_, C.preserves_acyclic ha, C.doubledArea_eq ha hsum, C.strictRank_lt ha,
    fun m => xQShift_injective m (hcol m), hor⟩

end VerticalStripLLT.Circular.Diagram
