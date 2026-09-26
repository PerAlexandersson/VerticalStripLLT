import VerticalStripLLT.Circular.NDSeparatedBasic
set_option backward.isDefEq.respectTransparency false


/-! The hypotheses of the separated ND branch and the residue separation of the main and
parallel contact paths, derived from acyclicity of the source and the separation
hypothesis `hsep`. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ}

/-- The hypotheses of the separated ND reduction, bundled. -/
structure NDSeparatedHyp (D : Diagram n) (t x : ℤ) (k : ℕ) : Prop where
  ha : D.edgeData.Admissible ∅
  ht : D.EligibleDE t
  h : ReverseBounceN D t x k
  hx : ¬ D.strictAt x
  hx1 : D.strictAt (x + 1)
  hsep : ∀ i ≤ k, D.residue (D.boundary^[i] t) ≠ D.residue (x + 1)

namespace NDSeparatedHyp

variable {D : Diagram n} {t x : ℤ} {k : ℕ} (H : NDSeparatedHyp D t x k)
include H

theorem iterate_spec : x = D.boundary^[k + 1] t ∧
    (∀ i, 1 ≤ i → i ≤ k → D.DDContact (D.boundary^[i] t)) ∧
    D.eastGap x = 0 ∧ ¬ (D.strictAt x ∧ D.strictAt (x + 1)) :=
  (D.reverseBounceN_iff_iterate).mp H.h

theorem x_eq : x = D.boundary^[k + 1] t := H.iterate_spec.1

theorem dd {i : ℕ} (h1 : 1 ≤ i) (hk : i ≤ k) : D.DDContact (D.boundary^[i] t) :=
  H.iterate_spec.2.1 i h1 hk

theorem gap_x : D.eastGap x = 0 := H.iterate_spec.2.2.1

theorem strict_iter {i : ℕ} (hi : i ≤ k) : D.strictAt (D.boundary^[i] t) := by
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · exact H.ht.1
  · exact (H.dd h0 hi).2.1

theorem strict_iter_succ {i : ℕ} (h1 : 1 ≤ i) (hi : i ≤ k + 1) :
    D.strictAt (D.boundary^[i] t + 1) := by
  rcases Nat.lt_or_ge i (k + 1) with h | h
  · exact (H.dd h1 (by lia)).2.2
  · obtain rfl : i = k + 1 := by lia
    rw [← H.x_eq]
    exact H.hx1

omit H in
theorem iterate_succ_eq (D : Diagram n) (t : ℤ) (i : ℕ) :
    D.boundary^[i + 1] t = D.boundary (D.boundary^[i] t) :=
  Function.iterate_succ_apply' _ _ _

theorem boundary_x1 : D.boundary (x + 1) = D.boundary x := by
  have hg := H.gap_x
  unfold eastGap at hg
  rw [ite_eq_right H.hx] at hg
  lia

theorem area_x1 : D.area.area (D.residue (x + 1)) = D.area.area (D.residue x) + 1 := by
  have hb := H.boundary_x1
  unfold boundary at hb
  lia

theorem res_x1_ne_x : D.residue (x + 1) ≠ D.residue x := D.residue_ne_of_strictAt H.hx1 H.hx

theorem res_t_ne_x : D.residue t ≠ D.residue x := D.residue_ne_of_strictAt H.ht.1 H.hx

theorem res_t_ne_x1 : D.residue t ≠ D.residue (x + 1) := H.hsep 0 (Nat.zero_le _)

theorem iter_ne_x {i : ℕ} (hi : i ≤ k) : D.residue (D.boundary^[i] t) ≠ D.residue x :=
  D.residue_ne_of_strictAt (H.strict_iter hi) H.hx

theorem iter_succ_ne_x {i : ℕ} (h1 : 1 ≤ i) (hi : i ≤ k + 1) :
    D.residue (D.boundary^[i] t + 1) ≠ D.residue x :=
  D.residue_ne_of_strictAt (H.strict_iter_succ h1 hi) H.hx

theorem iter_succ_ne_x1 {i : ℕ} (hi : i ≤ k) :
    D.residue (D.boundary^[i] t + 1) ≠ D.residue (x + 1) := by
  intro h
  rw [D.residue_succ, D.residue_succ] at h
  exact H.iter_ne_x hi (D.area.next_injective h)

theorem sel_main {i : ℕ} (hi : i ≤ k) :
    D.edgeData.selected ∅ (D.residue (D.boundary^[i + 1] t))
      (D.residue (D.boundary^[i] t)) := by
  rw [iterate_succ_eq]
  exact D.selected_of_strictAt (H.strict_iter hi)

theorem sel_par {i : ℕ} (h1 : 1 ≤ i) (hi : i ≤ k) :
    D.edgeData.selected ∅ (D.residue (D.boundary^[i + 1] t + 1))
      (D.residue (D.boundary^[i] t + 1)) := by
  rw [iterate_succ_eq]
  obtain ⟨hg, h1', h2⟩ := H.dd h1 hi
  exact D.parallel_selected_of_dd hg h1' h2

theorem sel_top : D.edgeData.selected ∅ (D.residue (D.boundary x)) (D.residue (x + 1)) := by
  rw [← H.boundary_x1]
  exact D.selected_of_strictAt H.hx1

theorem area_x_pos : 1 ≤ D.area.area (D.residue x) := by
  by_contra hc
  have hz : D.area.area (D.residue x) = 0 := by lia
  have hb : D.boundary x = x := by
    unfold boundary
    rw [hz]
    simp
  have h1 := H.sel_top
  have h2 := H.sel_main (le_refl k)
  rw [← H.x_eq] at h2
  rw [hb] at h1
  exact H.hsep k le_rfl (D.strict_selected_rightUnique h1 h2).symm

/-! ### Separation of the contact rows -/

theorem main_transGen {i j : ℕ} (hij : i < j) (hj : j ≤ k + 1) :
    Relation.TransGen (D.edgeData.selected ∅) (D.residue (D.boundary^[j] t))
      (D.residue (D.boundary^[i] t)) := by
  induction j with
  | zero => lia
  | succ j ih =>
    rcases Nat.lt_or_ge i j with h | h
    · exact Relation.TransGen.head (H.sel_main (by lia)) (ih h (by lia))
    · obtain rfl : i = j := by lia
      exact Relation.TransGen.single (H.sel_main (by lia))

theorem main_ne {i j : ℕ} (hij : i ≠ j) (hi : i ≤ k + 1) (hj : j ≤ k + 1) :
    D.residue (D.boundary^[i] t) ≠ D.residue (D.boundary^[j] t) := by
  intro heq
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have hc := H.main_transGen h hj
    rw [← heq] at hc
    exact H.ha _ hc
  · have hc := H.main_transGen h hi
    rw [heq] at hc
    exact H.ha _ hc

theorem par_ne {i j : ℕ} (hij : i ≠ j) (hi : i ≤ k + 1) (hj : j ≤ k + 1) :
    D.residue (D.boundary^[i] t + 1) ≠ D.residue (D.boundary^[j] t + 1) := by
  intro heq
  rw [D.residue_succ, D.residue_succ] at heq
  exact H.main_ne hij hi hj (D.area.next_injective heq)

theorem cross_ne_aux (s : ℕ) : ∀ i j : ℕ, (k + 1 - i) + (k + 1 - j) = s →
    i ≤ k + 1 →
    1 ≤ j → j ≤ k + 1 → D.residue (D.boundary^[i] t) ≠ D.residue (D.boundary^[j] t + 1) := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro i j hs hi hj1 hj heq
    rcases Nat.lt_or_ge i (k + 1) with hi' | hi'
    · rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
      · have h1 := H.sel_main (i := i) (by lia)
        have h2 := H.sel_par (i := j) hj1 (by lia)
        rw [heq] at h1
        exact ih _ (by lia) (i + 1) (j + 1) rfl (by lia) (by lia) (by lia)
          (D.strict_selected_leftUnique h1 h2)
      · obtain rfl : j = k + 1 := by lia
        rw [← H.x_eq] at heq
        exact H.hsep i (by lia) heq
    · obtain rfl : i = k + 1 := by lia
      rw [← H.x_eq] at heq
      exact H.iter_succ_ne_x hj1 hj heq.symm

theorem cross_ne {i j : ℕ} (hi : i ≤ k + 1) (hj1 : 1 ≤ j) (hj : j ≤ k + 1) :
    D.residue (D.boundary^[i] t) ≠ D.residue (D.boundary^[j] t + 1) :=
  H.cross_ne_aux _ i j rfl hi hj1 hj

theorem top_ne_main {i : ℕ} (h1 : 1 ≤ i) (hi : i ≤ k + 1) :
    D.residue (D.boundary x) ≠ D.residue (D.boundary^[i] t) := by
  intro heq
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by lia⟩
  have h1 := H.sel_main (i := i) (by lia)
  have h2 := H.sel_top
  rw [heq] at h2
  exact H.hsep i (by lia) (D.strict_selected_rightUnique h1 h2)

theorem par_reach (d : ℕ) (hd : d ≤ k) :
    Relation.ReflTransGen (D.edgeData.selected ∅) (D.residue (x + 1))
      (D.residue (D.boundary^[k + 1 - d] t + 1)) := by
  induction d with
  | zero =>
    rw [Nat.sub_zero, ← H.x_eq]
  | succ d ih =>
    have hstep := H.sel_par (i := k - d - 1 + 1) (by lia) (by lia)
    rw [show k - d - 1 + 1 + 1 = k + 1 - d by lia, show k - d - 1 + 1 = k + 1 - (d + 1) by lia]
      at hstep
    exact Relation.ReflTransGen.tail (ih (by lia)) hstep

theorem top_ne_par {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ k + 1) :
    D.residue (D.boundary x) ≠ D.residue (D.boundary^[j] t + 1) := by
  intro heq
  have hr := H.par_reach (k + 1 - j) (by lia)
  rw [show k + 1 - (k + 1 - j) = j by lia, ← heq] at hr
  exact H.ha _ (Relation.TransGen.head' H.sel_top hr)

end NDSeparatedHyp

end VerticalStripLLT.Circular.Diagram

