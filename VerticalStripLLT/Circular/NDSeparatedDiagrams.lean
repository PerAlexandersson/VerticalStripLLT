import VerticalStripLLT.Circular.NDSeparatedContacts
set_option backward.isDefEq.respectTransparency false


/-! The actual diagrams of the separated ND reduction: `N` (unstrict `g`), `E` (delete `g`),
`S` (strictify the lowered corner of `E`), `J` (delete that corner of `E`) and `Q` (shorten the
original root), with their rows, and the transport of the counted bounce to `N`, `S`, `J`. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ}

theorem ndSep_residue_boundary_congr' (P : Diagram n) {z w : ℤ}
    (h : P.residue z = P.residue w) : P.residue (P.boundary z) = P.residue (P.boundary w) := by
  simpa using P.ndSep_residue_boundary_congr h 0

theorem ndSep_update_le (f : Fin n → ℕ) (a : Fin n) (v : Fin n) :
    Function.update f a (f a - 1) v ≤ f v := by
  by_cases h : v = a
  · subst h
    simp
  · rw [Function.update_of_ne h]

/-- Transport of a counted reverse bounce to a diagram agreeing with `D` away from the
terminal rows `x` and `x + 1`. -/
theorem ndSep_reverseBounceN_transfer {D P : Diagram n} {t x : ℤ} {k : ℕ}
    (H : NDSeparatedHyp D t x k)
    (harea : ∀ v, v ≠ D.residue x → v ≠ D.residue (x + 1) → P.area.area v = D.area.area v)
    (hstrict : ∀ z, D.residue z ≠ D.residue x → D.residue z ≠ D.residue (x + 1) →
      (P.strictAt z ↔ D.strictAt z))
    (hgap : P.eastGap x = 0) (hnot : ¬ (P.strictAt x ∧ P.strictAt (x + 1))) :
    ReverseBounceN P t x k := by
  have hb : ∀ z, D.residue z ≠ D.residue x → D.residue z ≠ D.residue (x + 1) →
      P.boundary z = D.boundary z := by
    intro z h1 h2
    unfold boundary
    change z - (P.area.area (D.residue z) : ℤ) = _
    rw [harea _ h1 h2]
  have hiter : ∀ i ≤ k + 1, P.boundary^[i] t = D.boundary^[i] t := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [NDSeparatedHyp.iterate_succ_eq, NDSeparatedHyp.iterate_succ_eq, ih (by lia)]
      exact hb _ (H.iter_ne_x (by lia)) (H.hsep i (by lia))
  rw [P.reverseBounceN_iff_iterate]
  refine ⟨?_, ?_, hgap, hnot⟩
  · rw [hiter _ le_rfl]
    exact H.x_eq
  · intro i h1 hi
    rw [hiter i (by lia)]
    obtain ⟨hg, hs1, hs2⟩ := H.dd h1 hi
    have hr1 := H.iter_ne_x (i := i) (by lia)
    have hr2 := H.hsep i (by lia)
    have hr3 := H.iter_succ_ne_x h1 (by lia : i ≤ k + 1)
    have hr4 := H.iter_succ_ne_x1 (i := i) (by lia)
    refine ⟨?_, (hstrict _ hr1 hr2).mpr hs1, (hstrict _ hr3 hr4).mpr hs2⟩
    unfold eastGap at hg ⊢
    rw [hb _ hr1 hr2, hb _ hr3 hr4, ite_eq_left ((hstrict _ hr1 hr2).mpr hs1)]
    rw [ite_eq_left hs1] at hg
    exact hg

namespace NDSeparatedHyp

variable {D : Diagram n} {t x : ℤ} {k : ℕ} (H : NDSeparatedHyp D t x k)

/-- The terminal strict edge at the row `x + 1`. -/
noncomputable def g : Edge D.area := Classical.choose H.hx1

theorem g_mem : H.g ∈ D.strict := (Classical.choose_spec H.hx1).1

theorem g_head : H.g.head = D.residue (x + 1) := (Classical.choose_spec H.hx1).2

/-- `N`: the terminal strict edge made normal. -/
noncomputable def dN : Diagram n := D.unstrict H.g H.g_mem

/-- `E`: the terminal strict corner deleted. -/
noncomputable def dE : Diagram n := D.deleteCorner H.g (D.strict_corner H.g H.g_mem)

theorem dN_area : H.dN.area.area = D.area.area := rfl

theorem dN_strictAt (z : ℤ) :
    H.dN.strictAt z ↔ D.strictAt z ∧ D.residue z ≠ D.residue (x + 1) := by
  rw [← H.g_head]
  exact D.unstrict_strictAt_iff H.g H.g_mem z

theorem dE_area : H.dE.area.area = Function.update D.area.area (D.residue (x + 1))
    (D.area.area (D.residue (x + 1)) - 1) := by
  rw [← H.g_head]
  rfl

theorem dE_strictAt (z : ℤ) :
    H.dE.strictAt z ↔ D.strictAt z ∧ D.residue z ≠ D.residue (x + 1) := by
  rw [← H.g_head]
  exact D.deleteStrictCorner_strictAt_iff H.g H.g_mem z

theorem dE_area_x : H.dE.area.area (D.residue x) = D.area.area (D.residue x) := by
  rw [H.dE_area, Function.update_of_ne H.res_x1_ne_x.symm]

theorem dE_area_x1 : H.dE.area.area (D.residue (x + 1)) = D.area.area (D.residue x) := by
  rw [H.dE_area, Function.update_self, H.area_x1]
  simp

theorem dE_pos : 0 < H.dE.area.area (D.residue x) := by
  rw [H.dE_area_x]
  exact H.area_x_pos

/-- The corner of `E` at the row `x`, created by deleting `g`. -/
noncomputable def ell : Edge H.dE.area := H.dE.ndSepCornerAt (D.residue x) H.dE_pos

theorem ell_head : H.ell.head = D.residue x := rfl

theorem ell_corner : IsCorner H.ell := by
  apply H.dE.ndSepCornerAt_isCorner
  rw [next_congr H.dE.area D.area, ← D.residue_succ, H.dE_area_x1, H.dE_area_x]

theorem ell_not_mem : H.ell ∉ H.dE.strict :=
  H.dE.ndSepCornerAt_not_mem (z := x) H.dE_pos (fun h => H.hx ((H.dE_strictAt x).mp h).1)

/-- `S`: the lowered strict corner (the actual lower-strict diagram). -/
noncomputable def dS : Diagram n := H.dE.strictify H.ell H.ell_corner

/-- `J`: the lowered corner deleted from `E`. -/
noncomputable def dJ : Diagram n := H.dE.deleteCorner H.ell H.ell_corner

theorem dS_area : H.dS.area.area = Function.update D.area.area (D.residue (x + 1))
    (D.area.area (D.residue (x + 1)) - 1) := H.dE_area

theorem dS_strictAt (z : ℤ) : H.dS.strictAt z ↔
    (D.strictAt z ∧ D.residue z ≠ D.residue (x + 1)) ∨ D.residue z = D.residue x := by
  rw [dS, ndSep_strictify_strictAt_iff, H.dE_strictAt]
  rfl

theorem dJ_area : H.dJ.area.area = Function.update (Function.update D.area.area
    (D.residue (x + 1)) (D.area.area (D.residue (x + 1)) - 1)) (D.residue x)
    (D.area.area (D.residue x) - 1) := by
  rw [dJ, ndSep_deleteCorner_area, ell_head, H.dE_area_x, H.dE_area]

theorem dJ_strictAt (z : ℤ) :
    H.dJ.strictAt z ↔ D.strictAt z ∧ D.residue z ≠ D.residue (x + 1) := by
  rw [dJ, ndSep_deleteCorner_strictAt_iff_of_not_mem _ _ _ H.ell_not_mem, H.dE_strictAt]

/-- `Q`: the original root shortened. -/
noncomputable def dQ : Diagram n := D.shortenEligible t H.ht

theorem dQ_area : H.dQ.area.area =
    Function.update D.area.area (D.residue t) (D.area.area (D.residue t) - 1) :=
  D.shortenEligible_area t H.ht

theorem dQ_strictAt (z : ℤ) : H.dQ.strictAt z ↔ D.strictAt z :=
  D.shortenEligible_strictAt_iff t H.ht z

/-! ### Row agreement away from the terminal rows -/

theorem dS_area_eq {v : Fin n} (h2 : v ≠ D.residue (x + 1)) :
    H.dS.area.area v = D.area.area v := by
  rw [H.dS_area, Function.update_of_ne h2]

theorem dJ_area_eq {v : Fin n} (h1 : v ≠ D.residue x) (h2 : v ≠ D.residue (x + 1)) :
    H.dJ.area.area v = D.area.area v := by
  rw [H.dJ_area, Function.update_of_ne h1, Function.update_of_ne h2]

theorem dS_strictAt_eq {z : ℤ} (h1 : D.residue z ≠ D.residue x)
    (h2 : D.residue z ≠ D.residue (x + 1)) : H.dS.strictAt z ↔ D.strictAt z := by
  rw [H.dS_strictAt]
  tauto

theorem dN_strictAt_eq {z : ℤ} (h2 : D.residue z ≠ D.residue (x + 1)) :
    H.dN.strictAt z ↔ D.strictAt z := by
  rw [H.dN_strictAt]
  tauto

theorem dJ_strictAt_eq {z : ℤ} (h2 : D.residue z ≠ D.residue (x + 1)) :
    H.dJ.strictAt z ↔ D.strictAt z := by
  rw [H.dJ_strictAt]
  tauto

/-! ### Terminal rows -/

theorem dN_gap : H.dN.eastGap x = 0 := by
  have hg := H.gap_x
  have hs : ¬ H.dN.strictAt x := fun h => H.hx ((H.dN_strictAt x).mp h).1
  unfold eastGap at hg ⊢
  rw [ite_eq_right H.hx] at hg
  rw [ite_eq_right hs]
  exact hg

theorem dS_gap : H.dS.eastGap x = 0 := by
  have hs : H.dS.strictAt x := (H.dS_strictAt x).mpr (Or.inr rfl)
  unfold eastGap boundary
  rw [ite_eq_left hs]
  change x + 1 - (H.dS.area.area (D.residue (x + 1)) : ℤ) -
    (x - (H.dS.area.area (D.residue x) : ℤ)) - 1 = 0
  rw [H.dS_area_eq H.res_x1_ne_x.symm]
  have h1 : H.dS.area.area (D.residue (x + 1)) = D.area.area (D.residue x) := H.dE_area_x1
  rw [h1]
  ring

theorem dJ_gap : H.dJ.eastGap x = 0 := by
  have hs : ¬ H.dJ.strictAt x := fun h => H.hx ((H.dJ_strictAt x).mp h).1
  unfold eastGap boundary
  rw [ite_eq_right hs]
  change x + 1 - (H.dJ.area.area (D.residue (x + 1)) : ℤ) -
    (x - (H.dJ.area.area (D.residue x) : ℤ)) - 0 = 0
  have h1 : H.dJ.area.area (D.residue (x + 1)) = D.area.area (D.residue x) := by
    rw [H.dJ_area, Function.update_of_ne H.res_x1_ne_x, Function.update_self, H.area_x1]
    simp
  have h2 : H.dJ.area.area (D.residue x) = D.area.area (D.residue x) - 1 := by
    rw [H.dJ_area, Function.update_self]
  have hp := H.area_x_pos
  rw [h1, h2]
  lia

theorem dN_hx : ¬ H.dN.strictAt x := fun h => H.hx ((H.dN_strictAt x).mp h).1

theorem dN_hx1 : ¬ H.dN.strictAt (x + 1) := fun h => ((H.dN_strictAt _).mp h).2 rfl

theorem dJ_hx : ¬ H.dJ.strictAt x := fun h => H.hx ((H.dJ_strictAt x).mp h).1

theorem dJ_hx1 : ¬ H.dJ.strictAt (x + 1) := fun h => ((H.dJ_strictAt _).mp h).2 rfl

theorem dS_hx : H.dS.strictAt x := (H.dS_strictAt x).mpr (Or.inr rfl)

theorem dS_hx1 : ¬ H.dS.strictAt (x + 1) := by
  rw [H.dS_strictAt]
  rintro (⟨-, h⟩ | h)
  · exact h rfl
  · exact H.res_x1_ne_x h

/-! ### Counted bounces, eligibility and acyclicity of the intermediates -/

theorem dN_bounce : ReverseBounceN H.dN t x k :=
  ndSep_reverseBounceN_transfer H (fun _ _ _ => rfl)
    (fun _ _ h2 => H.dN_strictAt_eq h2) H.dN_gap (fun h => H.dN_hx h.1)

theorem dS_bounce : ReverseBounceN H.dS t x k :=
  ndSep_reverseBounceN_transfer H (fun _ _ h2 => H.dS_area_eq h2)
    (fun _ h1 h2 => H.dS_strictAt_eq h1 h2) H.dS_gap (fun h => H.dS_hx1 h.2)

theorem dJ_bounce : ReverseBounceN H.dJ t x k :=
  ndSep_reverseBounceN_transfer H (fun _ h1 h2 => H.dJ_area_eq h1 h2)
    (fun _ _ h2 => H.dJ_strictAt_eq h2) H.dJ_gap (fun h => H.dJ_hx h.1)

theorem dN_eligible : H.dN.EligibleDE t :=
  ndSep_eligible_transfer H.ht (H.dN_strictAt_eq H.res_t_ne_x1) rfl le_rfl

theorem dS_eligible : H.dS.EligibleDE t :=
  ndSep_eligible_transfer H.ht (H.dS_strictAt_eq H.res_t_ne_x H.res_t_ne_x1)
    (H.dS_area_eq H.res_t_ne_x1) (by rw [H.dS_area]; exact ndSep_update_le _ _ _)

theorem dJ_eligible : H.dJ.EligibleDE t :=
  ndSep_eligible_transfer H.ht (H.dJ_strictAt_eq H.res_t_ne_x1)
    (H.dJ_area_eq H.res_t_ne_x H.res_t_ne_x1)
    (by
      rw [H.dJ_area]
      refine le_trans ?_ (ndSep_update_le D.area.area (D.residue (x + 1)) (D.residue (t + 1)))
      by_cases hv : D.residue (t + 1) = D.residue x
      · rw [hv, Function.update_self, Function.update_of_ne H.res_x1_ne_x.symm]
        lia
      · rw [Function.update_of_ne hv])

theorem dN_admissible : H.dN.edgeData.Admissible ∅ :=
  ndSep_admissible_of_rows H.ha fun z hz => ⟨((H.dN_strictAt z).mp hz).1, rfl⟩

theorem dJ_admissible : H.dJ.edgeData.Admissible ∅ := by
  apply ndSep_admissible_of_rows H.ha
  intro z hz
  obtain ⟨hs, h2⟩ := (H.dJ_strictAt z).mp hz
  exact ⟨hs, H.dJ_area_eq (D.residue_ne_of_strictAt hs H.hx) h2⟩

end NDSeparatedHyp

end VerticalStripLLT.Circular.Diagram


