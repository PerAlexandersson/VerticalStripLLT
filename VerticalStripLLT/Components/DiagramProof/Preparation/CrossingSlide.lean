import VerticalStripLLT.Components.DiagramProof.Preparation.CrossingCore
import VerticalStripLLT.Components.DiagramProof.Preparation.CrossingTransforms
import VerticalStripLLT.Components.DiagramProof.Preparation.OrientationRestoration

/-!
# Crossing slide with restored exterior

For `a < b < c < d`, retain covers `ac` and `bd` while exchanging `ab` for `cd`.
We sweep the left and right obstructions, perform two central flips, then replay
the right sweep and then the left sweep backward. The endpoint formula restores
every other selected edge.
-/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

/-- A crossing slide is an actual flip path with its entire exterior restored. -/
theorem exists_crossingSlide (hforward : Forward D) (θ : Orientation D)
    (a b c d : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hac : Cover θ a c) (hbd : Cover θ b d)
    (hsab : D.edgeData.selected θ.val a b) (hncd : ¬ D.edgeData.selected θ.val c d) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      Cover η a c ∧ Cover η b d ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        exchangeRelation (D.edgeData.selected θ.val) a b c d u v) := by
  obtain ⟨L, hleftTrace, hLac, hL⟩ := exists_outgoingSweep_trace hforward θ a b c hab hbc hac
  have hLbd : Cover L b d := by
    apply (relationCover_congr_on_interval
      (fun {_ _} h => θ.selected_lt_of_forward hforward h)
      (fun {_ _} h => L.selected_lt_of_forward hforward h)
      (lo := b) (hi := d) ?_ le_rfl le_rfl).mp hbd
    intro u v hbu _
    exact ((hL u v).trans (outgoingSweepRelation_agree_above hab hbu)).symm
  obtain ⟨M, hrightTrace, hMbd, hM⟩ := exists_incomingSweep_trace hforward L b c d hbc hcd hLbd
  have hMac : Cover M a c := by
    apply (relationCover_congr_on_interval
      (fun {_ _} h => L.selected_lt_of_forward hforward h)
      (fun {_ _} h => M.selected_lt_of_forward hforward h)
      (lo := a) (hi := c) ?_ le_rfl le_rfl).mp hLac
    intro u v _ hvc
    exact ((hM u v).trans (incomingSweepRelation_agree_below hcd hvc)).symm
  have hMab : D.edgeData.selected M.val a b := by
    apply (hM a b).mpr
    apply (incomingSweepRelation_agree_below hcd hbc.le).mpr
    exact (hL a b).mpr ((outgoingSweepRelation_at_boundary _ a b c).mpr hsab)
  have hMncd : ¬ D.edgeData.selected M.val c d := by
    intro h
    apply hncd
    have hl := (incomingSweepRelation_at_boundary _ b c d).mp ((hM c d).mp h)
    exact (outgoingSweepRelation_agree_above hab hbc.le).mp ((hL c d).mp hl)
  have hMleft : ∀ w, a < w → w < b → ¬ D.edgeData.selected M.val a w := by
    intro w _ hwb h
    have hl := (incomingSweepRelation_agree_below hcd (hwb.trans hbc).le).mp
      ((hM a w).mp h)
    exact outgoingSweepRelation_no_earlier _ hwb ((hL a w).mp hl)
  have hMright : ∀ w, c < w → w < d → ¬ D.edgeData.selected M.val w d := by
    intro w hcw _ h
    exact incomingSweepRelation_no_later _ hcw ((hM w d).mp h)
  obtain ⟨P, hcentral, hPac, hPbd, hP⟩ :=
    exists_preparedCrossing hforward M a b c d hab hbc hcd hMac hMbd hMab hMncd
      hMleft hMright
  have hlocal : ∀ (S : Fin n → Fin n → Prop) u v, b ≤ u → v < d →
      (exchangeRelation S a b c d u v ↔ S u v) := by
    intro S u v hbu hvd
    have hua : u ≠ a := (hab.trans_le hbu).ne.symm
    simp only [exchangeRelation, hvd.ne, hua, false_and, and_false, false_or,
      not_false_eq_true, and_true]
  have hold : ∀ (S : Fin n → Fin n → Prop) w, c < w → w < d →
      (exchangeRelation S a b c d w d ↔ S w d) := by
    intro S w hcw _
    have hwc : w ≠ c := hcw.ne.symm
    have hwa : w ≠ a := (hab.trans (hbc.trans hcw)).ne.symm
    simp only [exchangeRelation, hwc, hwa, false_and, false_or, not_false_eq_true, and_true]
  have hcommute : ∀ (S : Fin n → Fin n → Prop) w, c < w → w < d → ∀ u v,
      exchangeRelation (exchangeRelation S w d b w) a b c d u v ↔
        exchangeRelation (exchangeRelation S a b c d) w d b w u v := by
    intro S w hcw _ u v
    exact exchangeRelation_commute S
      (fun h => hcw.ne.symm (congrArg Prod.fst h))
      (fun h => hab.ne.symm (congrArg Prod.fst h)) u v
  obtain ⟨Z, hrestoreRight, hZbd, hZ⟩ := restore_orientationIncomingSweep hforward hrightTrace
    (fun S => exchangeRelation S a b c d) (fun _ _ h => exchangeRelation_congr h a b c d)
    hlocal hold hcommute P hPbd hP
  have hZac : Cover Z a c := by
    apply (relationCover_congr_on_interval
      (fun {_ _} h => P.selected_lt_of_forward hforward h)
      (fun {_ _} h => Z.selected_lt_of_forward hforward h)
      (lo := a) (hi := c) ?_ le_rfl le_rfl).mp hPac
    intro u v _ hvc
    exact (hP u v).trans ((exchangeRelation_congr_at
      ((hM u v).trans (incomingSweepRelation_agree_below hcd hvc))).trans (hZ u v).symm)
  have hlocalLeft : ∀ (S : Fin n → Fin n → Prop) u v, a < u → v ≤ c →
      (exchangeRelation S a b c d u v ↔ S u v) := by
    intro S u v hau hvc
    exact exchangeRelation_iff_of_untouched S (fun h => hau.ne.symm h.1)
      (fun h => (hvc.trans_lt hcd).ne h.2)
  have holdLeft : ∀ (S : Fin n → Fin n → Prop) w, a < w → w < b →
      (exchangeRelation S a b c d a w ↔ S a w) := by
    intro S w _ hwb
    exact exchangeRelation_iff_of_untouched S (fun h => hwb.ne h.2)
      (fun h => (hab.trans hbc).ne h.1)
  have hcommuteLeft : ∀ (S : Fin n → Fin n → Prop) w, a < w → w < b → ∀ u v,
      exchangeRelation (exchangeRelation S a w w c) a b c d u v ↔
        exchangeRelation (exchangeRelation S a b c d) a w w c u v := by
    intro S w haw _ u v
    exact exchangeRelation_commute S
      (fun h => (hab.trans hbc).ne (congrArg Prod.fst h))
      (fun h => haw.ne.symm (congrArg Prod.fst h)) u v
  obtain ⟨η, hrestoreLeft, hηac, hη⟩ := restore_orientationOutgoingSweep hforward hleftTrace
    (fun S => exchangeRelation S a b c d) (fun _ _ h => exchangeRelation_congr h a b c d)
    hlocalLeft holdLeft hcommuteLeft Z hZac hZ
  have hηbd : Cover η b d := by
    apply (relationCover_congr_on_interval
      (fun {_ _} h => Z.selected_lt_of_forward hforward h)
      (fun {_ _} h => η.selected_lt_of_forward hforward h)
      (lo := b) (hi := d) ?_ le_rfl le_rfl).mp hZbd
    intro u v hbu _
    exact (hZ u v).trans ((exchangeRelation_congr_at
      ((hL u v).trans (outgoingSweepRelation_agree_above hab hbu))).trans (hη u v).symm)
  have hleftPath := outgoingSweepTrace_forget _ _ a b c hleftTrace
  have hrightPath := outgoingSweepTrace_forget (V := OrderDual (Fin n)) _ _ d c b hrightTrace
  exact ⟨η, hleftPath.trans
    (hrightPath.trans (hcentral.trans (hrestoreRight.trans hrestoreLeft))), hηac, hηbd, hη⟩

/-- In particular, the exact exchanged state belongs to the same whole flip component. -/
theorem crossingSlide_mem_component (hforward : Forward D) (θ : Orientation D)
    (a b c d : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hac : Cover θ a c) (hbd : Cover θ b d)
    (hsab : D.edgeData.selected θ.val a b) (hncd : ¬ D.edgeData.selected θ.val c d) :
    ∃ η ∈ flipComponent D θ, Cover η a c ∧ Cover η b d ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        exchangeRelation (D.edgeData.selected θ.val) a b c d u v) := by
  obtain ⟨η, hp, hηac, hηbd, hrel⟩ := exists_crossingSlide hforward θ a b c d hab hbc hcd
    hac hbd hsab hncd
  exact ⟨η, mem_flipComponent_iff.mpr hp, hηac, hηbd, hrel⟩

end VerticalStripLLT.Circular.DiagramProof
