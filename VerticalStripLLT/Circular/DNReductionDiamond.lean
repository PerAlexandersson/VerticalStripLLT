import VerticalStripLLT.Circular.StrictVals
import VerticalStripLLT.Circular.CornerDeleteRows
import VerticalStripLLT.Circular.DNReductionTarget
import VerticalStripLLT.Circular.DDResolvedRows
import VerticalStripLLT.Circular.DDResolvedStrict
import VerticalStripLLT.Circular.SecondBounceRecurrences

set_option backward.isDefEq.respectTransparency false

/-! The two sides of the DD/DN diamond at the last DD contact. -/

namespace VerticalStripLLT.Circular.Diagram.DDLocalData

open scoped Classical

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.DDLocalData t)

/-- Unstricting the old last-contact row of the source DN target gives the DN target
of the resolved child, whose root is the parallel row `boundary t + 1`. -/
theorem unstrict_isDNTarget {x : ℤ} {T : Diagram n} (hT : IsDNTarget D t x T)
    (c : Edge T.area) (hcT : c ∈ T.strict) (cH : c.head = D.residue (D.boundary t))
    (hab : D.residue (x + 1) ≠ D.residue (D.boundary t + 1))
    (hac : D.residue (x + 1) ≠ D.residue t)
    (hdb : D.residue x ≠ D.residue (D.boundary t + 1))
    (hdc : D.residue x ≠ D.residue t)
    (haP : D.residue (x + 1) ≠ D.residue (D.boundary t)) :
    IsDNTarget B.resolved (D.boundary t + 1) x (T.unstrict c hcT) := by
  have hbc : D.residue (D.boundary t + 1) ≠ D.residue t := by
    rw [← B.gh, ← B.fh]
    intro h
    exact B.hfg (D.strict_edge_eq_of_head_eq B.hf B.hg h.symm)
  have hsame : D.area.area (D.residue (D.boundary t + 1)) =
      D.area.area (D.residue (D.boundary t)) := by
    rw [D.residue_succ, ← B.eh]
    exact B.sameArea
  constructor
  · change T.area.area = Function.update (Function.update B.resolved.area.area
      (D.residue (x + 1)) (B.resolved.area.area (D.residue x) + 1))
      (D.residue (D.boundary t + 1)) (B.resolved.area.area (D.residue (D.boundary t + 1)) - 1)
    rw [hT.1, B.resolved_area]
    funext i
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · intro z
    rw [T.unstrict_strictAt_iff c hcT z, hT.2 z, residue_congr B.resolved D,
      B.resolved_strictAt_iff z, cH, residue_congr T D]
    by_cases hr : D.residue z = D.residue (x + 1)
    · rw [hr]
      simp [haP]
    · simp only [hr, or_false]
      tauto


/-- On the deletion side, a direct DN move at the old last DD contact takes the DN
target of the deleted child to the corner deletion of the source DN target. -/
theorem deleted_target_models {x : ℤ} {T : Diagram n} (hT : IsDNTarget D t x T)
    (c : Edge T.area) (hcT : c ∈ T.strict) (cH : c.head = D.residue (D.boundary t))
    {V : Diagram n} (hV : IsDNTarget B.deleted (D.boundary t) x V)
    (ht : D.EligibleDE t) (hc : D.strictAt (D.boundary t))
    (hab : D.residue (x + 1) ≠ D.residue (D.boundary t + 1))
    (hac : D.residue (x + 1) ≠ D.residue t)
    (hdb : D.residue x ≠ D.residue (D.boundary t + 1))
    (hdc : D.residue x ≠ D.residue t)
    (haP : D.residue (x + 1) ≠ D.residue (D.boundary t))
    (hdP : D.residue x ≠ D.residue (D.boundary t)) :
    (∀ m : ℕ, V.coloringLLT m = (T.deleteCorner c (T.strict_corner c hcT)).coloringLLT m) ∧
      shiftedOrientationExpansion V =
        shiftedOrientationExpansion (T.deleteCorner c (T.strict_corner c hcT)) := by
  have hbc : D.residue (D.boundary t + 1) ≠ D.residue t := by
    rw [← B.gh, ← B.fh]
    intro h
    exact B.hfg (D.strict_edge_eq_of_head_eq B.hf B.hg h.symm)
  have hsame : D.area.area (D.residue (D.boundary t + 1)) =
      D.area.area (D.residue (D.boundary t)) := by
    rw [D.residue_succ, ← B.eh]
    exact B.sameArea
  have hct := ht.2.1
  have hctn := D.area.bound (D.residue t)
  have hn : 2 ≤ n := by lia
  have hPb : D.residue (D.boundary t) ≠ D.residue (D.boundary t + 1) :=
    D.residue_p_ne_succ hn _
  have hPc : D.residue (D.boundary t) ≠ D.residue t := by
    intro hh
    have heq := D.eq_of_residue_eq_of_bounds hh.symm (by unfold boundary; lia)
      (by unfold boundary; lia)
    unfold boundary at heq
    lia
  have hPpos := D.strictAt_area_pos hc
  have hPlt := D.area.bound (D.residue (D.boundary t))
  have hgapt : D.area.area (D.residue (t + 1)) < D.area.area (D.residue t) := by
    rw [D.residue_succ, ← B.fh]
    exact B.rootGap
  have ht1x1 : D.residue (t + 1) ≠ D.residue (x + 1) := by
    intro h
    rw [D.residue_succ, D.residue_succ] at h
    exact hdc (D.area.next_injective h).symm
  have hEs : ∀ z, B.deleted.strictAt z ↔
      D.strictAt z ∧ D.residue z ≠ D.residue (D.boundary t + 1) := by
    intro z
    unfold deleted
    rw [D.deleteStrictCorner_strictAt_iff B.g B.hg z, B.gh]
  have hEa : B.deleted.area.area = Function.update D.area.area
      (D.residue (D.boundary t + 1)) (D.area.area (D.residue (D.boundary t + 1)) - 1) := by
    unfold deleted
    rw [area_deleteCorner, B.gh]
  have hVa : V.area.area = Function.update (Function.update (Function.update D.area.area
      (D.residue (D.boundary t + 1)) (D.area.area (D.residue (D.boundary t + 1)) - 1))
      (D.residue (x + 1)) (D.area.area (D.residue x) + 1))
      (D.residue (D.boundary t)) (D.area.area (D.residue (D.boundary t)) - 1) := by
    rw [hV.1, residue_congr B.deleted D, hEa]
    funext i
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  have hVs : ∀ z, V.strictAt z ↔
      ((D.strictAt z ∧ D.residue z ≠ D.residue (D.boundary t + 1)) ∧
      D.residue z ≠ D.residue x) ∨ D.residue z = D.residue (x + 1) := by
    intro z
    rw [hV.2 z, residue_congr B.deleted D, hEs z]
  have hnextV : ∀ z, V.area.next (D.residue z) = D.residue (z + 1) := by
    intro z
    simpa only [residue_congr V D] using (V.residue_succ z).symm
  obtain ⟨e1, he1, e1h⟩ : V.strictAt (D.boundary t) :=
    (hVs _).mpr (Or.inl ⟨⟨hc, hPb⟩, hdP.symm⟩)
  obtain ⟨f1, hf1, f1h⟩ : V.strictAt t :=
    (hVs _).mpr (Or.inl ⟨⟨ht.1, hbc.symm⟩, hdc.symm⟩)
  rw [residue_congr V D] at e1h f1h
  have hVp1 : ¬ V.strictAt (D.boundary t + 1) := by
    rw [hVs]
    simp [hab.symm]
  have hVP : V.area.area (D.residue (D.boundary t)) =
      D.area.area (D.residue (D.boundary t)) - 1 := by
    rw [hVa]
    simp
  have hVb : V.area.area (D.residue (D.boundary t + 1)) =
      D.area.area (D.residue (D.boundary t + 1)) - 1 := by
    rw [hVa]
    simp [hPb.symm, hab.symm]
  have hVt : V.area.area (D.residue t) = D.area.area (D.residue t) := by
    rw [hVa]
    simp [hPc.symm, hac.symm, hbc.symm]
  have hVt1 : V.area.area (D.residue (t + 1)) ≤ D.area.area (D.residue (t + 1)) := by
    rw [hVa]
    simp only [Function.update_apply, ht1x1, ite_false]
    split_ifs <;> lia
  have heq1 : V.area.area (V.area.next e1.head) = V.area.area e1.head := by
    rw [e1h, hnextV, hVb, hVP, hsame]
  have hb1 : V.area.area e1.head + 1 < n := by
    rw [e1h, hVP]
    lia
  have hns1 : ∀ g ∈ V.strict, g.head ≠ V.area.next e1.head := by
    intro g hg hh
    exact hVp1 ⟨g, hg, by rw [hh, e1h, hnextV, residue_congr V D]⟩
  have hlen1 : 2 ≤ f1.length.val := by
    rw [(V.strict_corner f1 hf1).1, f1h, hVt]
    exact hct
  have hgap1 : V.area.area (V.area.next f1.head) < V.area.area f1.head := by
    rw [f1h, hnextV, hVt]
    lia
  have hfe1 : f1 ≠ e1 := fun h =>
    hPc (e1h.symm.trans ((congrArg Edge.head h).symm.trans f1h))
  have hcontact1 : f1.tail = e1.head := by
    rw [V.strictEdge_tail_of_lift hf1 (by rw [residue_congr V D]; exact f1h), e1h,
      residue_congr V D]
    congr 1
    unfold boundary
    rw [residue_congr V D, hVt]
  have hW : V.dnSuccessor e1 f1 he1 hf1 hfe1 heq1 hb1 hns1 hlen1 hgap1 =
      T.deleteCorner c (T.strict_corner c hcT) := by
    apply ext_of_area_eq_of_strictAt
    · rw [V.dnSuccessor_area e1 f1 he1 hf1 hfe1 heq1 hb1 hns1 hlen1 hgap1, area_deleteCorner,
        e1h, f1h, hnextV, cH, hT.1, hVa]
      funext i
      simp only [Function.update_apply]
      split_ifs <;> simp_all
      lia
    · intro z
      rw [V.dnSuccessor_strictAt_iff e1 f1 he1 hf1 hfe1 heq1 hb1 hns1 hlen1 hgap1,
        T.deleteStrictCorner_strictAt_iff c hcT z, hVs z, hT.2 z, e1h, hnextV, cH,
        residue_congr V D, residue_congr T D]
      by_cases hr : D.residue z = D.residue (D.boundary t + 1)
      · have hs : D.strictAt z := (D.strictAt_congr_residue hr).mpr ⟨B.g, B.hg, B.gh⟩
        simp [hr, hs, hPb.symm, hdb.symm, hab.symm]
      · simp only [hr, or_false]
        tauto
  refine ⟨fun m => ?_, ?_⟩
  · rw [← hW]
    exact V.coloringLLT_dnSuccessor e1 f1 he1 hf1 hfe1 hcontact1 heq1 hb1 hns1 hlen1 hgap1 m
  · rw [← hW]
    exact V.shiftedOrientationExpansion_dnSuccessor e1 f1 he1 hf1 hfe1 hcontact1 heq1 hb1 hns1
      hlen1 hgap1

end VerticalStripLLT.Circular.Diagram.DDLocalData
