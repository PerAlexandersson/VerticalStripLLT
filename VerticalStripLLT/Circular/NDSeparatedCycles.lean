import VerticalStripLLT.Circular.NDSeparatedIdentities
set_option backward.isDefEq.respectTransparency false


/-! The lowered diagram `S` may be cyclic even though `D` is acyclic.  The strict graph of `Q`
is the neutral endpoint exchange of the strict graph of `S` along the separated inner main
path `x, …, t₁` and the parallel path `x + 1, …, t₁ + 1`, with outer endpoints the boundary of
`x` and the root `t` (which may coincide).  The inner-path hypotheses are derived from the
acyclicity of `D` and `hsep`, not from any acyclicity of `S`, so `S` and `Q` are acyclic
together. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ}

namespace NDSeparatedHyp

variable {D : Diagram n} {t x : ℤ} {k : ℕ} (H : NDSeparatedHyp D t x k)
include H

theorem dS_boundary_eq {z : ℤ} (h : D.residue z ≠ D.residue (x + 1)) :
    H.dS.boundary z = D.boundary z := by
  unfold boundary
  change z - (H.dS.area.area (D.residue z) : ℤ) = _
  rw [H.dS_area_eq h]

theorem dQ_boundary_eq {z : ℤ} (h : D.residue z ≠ D.residue t) :
    H.dQ.boundary z = D.boundary z := by
  unfold boundary
  change z - (H.dQ.area.area (D.residue z) : ℤ) = _
  rw [H.dQ_area, Function.update_of_ne h]

theorem dQ_boundary_root : H.dQ.boundary t = D.boundary t + 1 := by
  unfold boundary
  change t - (H.dQ.area.area (D.residue t) : ℤ) = t - (D.area.area (D.residue t) : ℤ) + 1
  rw [H.dQ_area, Function.update_self]
  have := H.ht.2.1
  lia

theorem dS_sel_iff {u : Fin n} {z : ℤ} (h1 : D.residue z ≠ D.residue x)
    (h2 : D.residue z ≠ D.residue (x + 1)) :
    H.dS.edgeData.selected ∅ u (D.residue z) ↔ D.edgeData.selected ∅ u (D.residue z) := by
  have e1 := H.dS.ndSep_selected_residue_iff u z
  have e2 := D.ndSep_selected_residue_iff u z
  rw [H.dS_boundary_eq h2, H.dS_strictAt_eq h1 h2] at e1
  exact e1.trans e2.symm

/-- The inner main path `x = t_{k+1}, …, t₁` of the exchange. -/
def exMain (i : Fin (k + 1)) : Fin n := D.residue (D.boundary^[k + 1 - i.val] t)

/-- The parallel path `x + 1, …, t₁ + 1` of the exchange. -/
def exPar (i : Fin (k + 1)) : Fin n := D.residue (D.boundary^[k + 1 - i.val] t + 1)

omit H in
theorem exMain_apply (i : Fin (k + 1)) :
    exMain (D := D) (t := t) (k := k) i = D.residue (D.boundary^[k + 1 - i.val] t) := rfl

omit H in
theorem exPar_apply (i : Fin (k + 1)) :
    exPar (D := D) (t := t) (k := k) i = D.residue (D.boundary^[k + 1 - i.val] t + 1) := rfl

theorem exMain_zero : exMain (D := D) (t := t) (k := k) 0 = D.residue x := by
  rw [exMain_apply, Fin.val_zero, Nat.sub_zero, ← H.x_eq]

theorem exPar_zero : exPar (D := D) (t := t) (k := k) 0 = D.residue (x + 1) := by
  rw [exPar_apply, Fin.val_zero, Nat.sub_zero, ← H.x_eq]

omit H in
theorem exMain_last : exMain (D := D) (t := t) (k := k) (Fin.last k) =
    D.residue (D.boundary t) := by
  rw [exMain_apply, Fin.val_last, show k + 1 - k = 1 by lia, Function.iterate_one]

omit H in
theorem exPar_last : exPar (D := D) (t := t) (k := k) (Fin.last k) =
    D.residue (D.boundary t + 1) := by
  rw [exPar_apply, Fin.val_last, show k + 1 - k = 1 by lia, Function.iterate_one]

/-- The strict graph of `Q` is the neutral endpoint exchange of the strict graph of `S`. -/
theorem dQ_selected_iff (u v : Fin n) :
    H.dQ.edgeData.selected ∅ u v ↔
      neutralExchangeRelation (H.dS.edgeData.selected ∅) (D.residue (D.boundary x))
        (D.residue t) (exMain (D := D) (t := t) (k := k))
        (exPar (D := D) (t := t) (k := k)) u v := by
  obtain ⟨w, rfl⟩ : ∃ w : ℤ, D.residue w = v :=
    ⟨v.val, Orientation.residue_intCast_eq v⟩
  unfold neutralExchangeRelation
  rw [H.exMain_zero, exMain_last, H.exPar_zero, exPar_last]
  have hQ : H.dQ.edgeData.selected ∅ u (D.residue w) ↔
      D.strictAt w ∧ u = D.residue (H.dQ.boundary w) := by
    rw [← H.dQ_strictAt w]
    exact H.dQ.ndSep_selected_residue_iff u w
  have hS : H.dS.edgeData.selected ∅ u (D.residue w) ↔
      H.dS.strictAt w ∧ u = D.residue (H.dS.boundary w) :=
    H.dS.ndSep_selected_residue_iff u w
  rw [hQ, hS]
  by_cases ht' : D.residue w = D.residue t
  · have hx1' : D.residue w ≠ D.residue (x + 1) := fun h => H.res_t_ne_x1 (ht'.symm.trans h)
    have hDw : D.strictAt w := (D.strictAt_congr_residue ht').mpr H.ht.1
    have hQb : D.residue (H.dQ.boundary w) = D.residue (D.boundary t + 1) := by
      rw [← H.dQ_boundary_root]
      exact H.dQ.ndSep_residue_boundary_congr' ht'
    rw [hQb, H.dS_boundary_eq hx1', D.ndSep_residue_boundary_congr' ht']
    constructor
    · rintro ⟨-, hu⟩
      exact Or.inr (Or.inr ⟨hu, ht'⟩)
    · rintro (⟨⟨-, hu⟩, -, hne⟩ | ⟨-, hw⟩ | ⟨hu, -⟩)
      · exact absurd ⟨hu, ht'⟩ hne
      · exact absurd hw hx1'
      · exact ⟨hDw, hu⟩
  · by_cases hx' : D.residue w = D.residue x
    · have hx1' : D.residue w ≠ D.residue (x + 1) := fun h => H.res_x1_ne_x (h.symm.trans hx')
      have hnD : ¬ D.strictAt w := fun h => H.hx ((D.strictAt_congr_residue hx').mp h)
      rw [H.dS_boundary_eq hx1', D.ndSep_residue_boundary_congr' hx']
      constructor
      · rintro ⟨h, -⟩
        exact absurd h hnD
      · rintro (⟨⟨-, hu⟩, hne, -⟩ | ⟨-, hw⟩ | ⟨-, hw⟩)
        · exact absurd ⟨hu, hx'⟩ hne
        · exact absurd hw hx1'
        · exact absurd hw ht'
    · by_cases hx1' : D.residue w = D.residue (x + 1)
      · have hDw : D.strictAt w := (D.strictAt_congr_residue hx1').mpr H.hx1
        have hnS : ¬ H.dS.strictAt w := fun h =>
          H.dS_hx1 ((H.dS.strictAt_congr_residue hx1').mp h)
        rw [H.dQ_boundary_eq ht', D.ndSep_residue_boundary_congr' hx1', H.boundary_x1]
        constructor
        · rintro ⟨-, hu⟩
          exact Or.inr (Or.inl ⟨hu, hx1'⟩)
        · rintro (⟨⟨h, -⟩, -⟩ | ⟨hu, -⟩ | ⟨-, hw⟩)
          · exact absurd h hnS
          · exact ⟨hDw, hu⟩
          · exact absurd hw ht'
      · rw [H.dQ_boundary_eq ht', H.dS_boundary_eq hx1', H.dS_strictAt_eq hx' hx1']
        constructor
        · intro h
          exact Or.inl ⟨h, fun h' => hx' h'.2, fun h' => ht' h'.2⟩
        · rintro (⟨h, -⟩ | ⟨-, hw⟩ | ⟨-, hw⟩)
          · exact h
          · exact absurd hw hx1'
          · exact absurd hw ht'

/-! ### The inner-path hypotheses of the exchange, from `D` and `hsep` -/

theorem exMain_injective : Function.Injective (exMain (D := D) (t := t) (k := k)) := by
  intro i j hij
  by_contra hne
  have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
  have hi := i.isLt
  have hj := j.isLt
  exact H.main_ne (i := k + 1 - i.val) (j := k + 1 - j.val) (by lia) (by lia) (by lia) hij

theorem exPar_injective : Function.Injective (exPar (D := D) (t := t) (k := k)) := by
  intro i j hij
  by_contra hne
  have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
  have hi := i.isLt
  have hj := j.isLt
  exact H.par_ne (i := k + 1 - i.val) (j := k + 1 - j.val) (by lia) (by lia) (by lia) hij

theorem exMain_ne_exPar (i j : Fin (k + 1)) :
    exMain (D := D) (t := t) (k := k) i ≠ exPar (D := D) (t := t) (k := k) j := by
  have hj := j.isLt
  exact H.cross_ne (i := k + 1 - i.val) (j := k + 1 - j.val) (by lia) (by lia) (by lia)

theorem start_ne_exMain (i : Fin (k + 1)) :
    D.residue (D.boundary x) ≠ exMain (D := D) (t := t) (k := k) i := by
  have hi := i.isLt
  exact H.top_ne_main (i := k + 1 - i.val) (by lia) (by lia)

theorem start_ne_exPar (i : Fin (k + 1)) :
    D.residue (D.boundary x) ≠ exPar (D := D) (t := t) (k := k) i := by
  have hi := i.isLt
  exact H.top_ne_par (j := k + 1 - i.val) (by lia) (by lia)

theorem root_ne_exMain (i : Fin (k + 1)) :
    D.residue t ≠ exMain (D := D) (t := t) (k := k) i := by
  have hi := i.isLt
  exact H.main_ne (i := 0) (j := k + 1 - i.val) (by lia) (by lia) (by lia)

theorem root_ne_exPar (i : Fin (k + 1)) :
    D.residue t ≠ exPar (D := D) (t := t) (k := k) i := by
  have hi := i.isLt
  exact H.cross_ne (i := 0) (j := k + 1 - i.val) (by lia) (by lia) (by lia)

theorem exMain_start :
    H.dS.edgeData.selected ∅ (D.residue (D.boundary x))
      (exMain (D := D) (t := t) (k := k) 0) := by
  rw [H.exMain_zero]
  refine (H.dS.ndSep_selected_residue_iff _ x).mpr ⟨H.dS_hx, ?_⟩
  rw [H.dS_boundary_eq H.res_x1_ne_x.symm]
  rfl

theorem exMain_end :
    H.dS.edgeData.selected ∅ (exMain (D := D) (t := t) (k := k) (Fin.last k)) (D.residue t) := by
  rw [exMain_last]
  exact (H.dS_sel_iff H.res_t_ne_x H.res_t_ne_x1).mpr (H.sel_main (i := 0) (by lia))

theorem exMain_chain (i : Fin k) :
    H.dS.edgeData.selected ∅ (exMain (D := D) (t := t) (k := k) i.castSucc)
      (exMain (D := D) (t := t) (k := k) i.succ) := by
  have hi := i.isLt
  rw [exMain_apply, exMain_apply, Fin.val_castSucc, Fin.val_succ,
    show k + 1 - i.val = k - i.val + 1 by lia, show k + 1 - (i.val + 1) = k - i.val by lia]
  exact (H.dS_sel_iff (H.iter_ne_x (by lia)) (H.hsep _ (by lia))).mpr
    (H.sel_main (i := k - i.val) (by lia))

theorem exPar_chain (i : Fin k) :
    H.dS.edgeData.selected ∅ (exPar (D := D) (t := t) (k := k) i.castSucc)
      (exPar (D := D) (t := t) (k := k) i.succ) := by
  have hi := i.isLt
  rw [exPar_apply, exPar_apply, Fin.val_castSucc, Fin.val_succ,
    show k + 1 - i.val = k - i.val + 1 by lia, show k + 1 - (i.val + 1) = k - i.val by lia]
  exact (H.dS_sel_iff (H.iter_succ_ne_x (by lia) (by lia)) (H.iter_succ_ne_x1 (by lia))).mpr
    (H.sel_par (i := k - i.val) (by lia) (by lia))

theorem exPar_start_free (u : Fin n) :
    ¬ H.dS.edgeData.selected ∅ u (exPar (D := D) (t := t) (k := k) 0) := by
  rw [H.exPar_zero]
  exact H.dS.not_selected_to_of_not_strictAt H.dS_hx1 u

theorem exPar_end_free (u : Fin n) :
    ¬ H.dS.edgeData.selected ∅ (exPar (D := D) (t := t) (k := k) (Fin.last k)) u := by
  rw [exPar_last]
  have h := H.dS_eligible.parallel_end_free H.dS u
  rw [H.dS_boundary_eq H.res_t_ne_x1] at h
  exact h

/-- `S` is acyclic exactly when `Q` is. -/
theorem dS_admissible_iff : H.dS.edgeData.Admissible ∅ ↔ H.dQ.edgeData.Admissible ∅ := by
  have hrel : H.dQ.edgeData.selected ∅ =
      neutralExchangeRelation (H.dS.edgeData.selected ∅) (D.residue (D.boundary x))
        (D.residue t) (exMain (D := D) (t := t) (k := k))
        (exPar (D := D) (t := t) (k := k)) := by
    funext u v
    exact propext (H.dQ_selected_iff u v)
  unfold EdgeData.Admissible
  rw [hrel]
  exact neutralExchange_acyclic_iff (H.dS.edgeData.selected ∅)
    H.dS.strict_selected_leftUnique H.dS.strict_selected_rightUnique _ _ _ _
    H.exMain_injective H.exPar_injective H.exMain_ne_exPar H.start_ne_exMain
    H.start_ne_exPar H.root_ne_exMain H.root_ne_exPar H.exMain_start H.exMain_end
    H.exMain_chain H.exPar_chain H.exPar_start_free H.exPar_end_free

end NDSeparatedHyp

end VerticalStripLLT.Circular.Diagram

