import VerticalStripLLT.Circular.AliasReductionSwap

set_option backward.isDefEq.respectTransparency false

/-! The exceptional normal pairs `B`, `C`, `H` and exterior boundary facts. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace AliasContacts

variable {n : ℕ} {D : Diagram n} (K : AliasContacts D)

/-- Source forced ascents `p_j → q_j`. -/
noncomputable def Bset : Finset (Fin n × Fin n) :=
  (Finset.range K.r).image fun j => (K.p j, K.q j)

/-- Target forced ascents `q_(j-1) → p_j`. -/
noncomputable def Cset : Finset (Fin n × Fin n) :=
  (Finset.Ico 1 K.r).image fun j => (K.q (j - 1), K.p j)

/-- The three source normal pairs removed by the alias target. -/
noncomputable def Hset : Finset (Fin n × Fin n) :=
  {(K.p (K.r - 1), K.p 0), (K.q (K.r - 1), K.p 0), (K.q (K.r - 1), K.q 0)}

noncomputable def XQset : Finset (Fin n × Fin n) := K.Bset ∪ K.Cset

noncomputable def Xset : Finset (Fin n × Fin n) := K.XQset ∪ K.Hset

theorem mem_Bset (x : Fin n × Fin n) : x ∈ K.Bset ↔ ∃ j < K.r, x = (K.p j, K.q j) := by
  simp only [Bset, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

theorem mem_Cset (x : Fin n × Fin n) :
    x ∈ K.Cset ↔ ∃ j, 1 ≤ j ∧ j < K.r ∧ x = (K.q (j - 1), K.p j) := by
  simp only [Cset, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, rfl⟩; exact ⟨j, h1, h2, rfl⟩
  · rintro ⟨j, h1, h2, rfl⟩; exact ⟨j, ⟨h1, h2⟩, rfl⟩

theorem mem_Hset (a b : Fin n) : (a, b) ∈ K.Hset ↔
    (b = K.p 0 ∧ (a = K.p (K.r - 1) ∨ a = K.q (K.r - 1))) ∨
      (b = K.q 0 ∧ a = K.q (K.r - 1)) := by
  simp only [Hset, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  tauto

theorem mem_Xset (x : Fin n × Fin n) : x ∈ K.Xset ↔ x ∈ K.XQset ∨ x ∈ K.Hset := by
  simp [Xset]

theorem mem_XQ_head_p (j : ℕ) (hj : j < K.r) (a : Fin n) :
    (a, K.p j) ∈ K.XQset ↔ 1 ≤ j ∧ a = K.q (j - 1) := by
  simp only [XQset, Finset.mem_union, mem_Bset, mem_Cset, Prod.mk.injEq]
  constructor
  · rintro (⟨i, hi, _, h⟩ | ⟨i, h1, h2, ha, h⟩)
    · exact False.elim (K.p_ne_q hj hi h)
    · have := K.p_inj hj h2 h
      subst this
      exact ⟨h1, ha⟩
  · rintro ⟨h1, ha⟩
    exact Or.inr ⟨j, h1, hj, ha, rfl⟩

theorem mem_XQ_head_q (j : ℕ) (hj : j < K.r) (a : Fin n) :
    (a, K.q j) ∈ K.XQset ↔ a = K.p j := by
  simp only [XQset, Finset.mem_union, mem_Bset, mem_Cset, Prod.mk.injEq]
  constructor
  · rintro (⟨i, hi, ha, h⟩ | ⟨i, _, h2, _, h⟩)
    · have := K.q_inj hj hi h
      subst this
      exact ha
    · exact absurd h (K.p_ne_q h2 hj).symm
  · rintro ha
    exact Or.inl ⟨j, hj, ha, rfl⟩

theorem not_mem_XQ_ext (b : Fin n) (hb : ∀ j < K.r, b ≠ K.p j ∧ b ≠ K.q j) (a : Fin n) :
    (a, b) ∉ K.XQset := by
  simp only [XQset, Finset.mem_union, mem_Bset, mem_Cset, Prod.mk.injEq]
  rintro (⟨i, hi, _, h⟩ | ⟨i, _, h2, _, h⟩)
  · exact (hb i hi).2 h
  · exact (hb i h2).1 h

theorem not_mem_H_ext (b : Fin n) (hb : ∀ j < K.r, b ≠ K.p j ∧ b ≠ K.q j) (a : Fin n) :
    (a, b) ∉ K.Hset := by
  rw [mem_Hset]
  rintro (⟨h, _⟩ | ⟨h, _⟩)
  · exact (hb 0 K.r_pos).1 h
  · exact (hb 0 K.r_pos).2 h

theorem not_mem_X_ext (b : Fin n) (hb : ∀ j < K.r, b ≠ K.p j ∧ b ≠ K.q j) (a : Fin n) :
    (a, b) ∉ K.Xset := by
  rw [mem_Xset]
  rintro (h | h)
  · exact K.not_mem_XQ_ext b hb a h
  · exact K.not_mem_H_ext b hb a h

theorem mem_X_head_p_succ (i : ℕ) (hi : i + 1 < K.r) (a : Fin n) :
    (a, K.p (i + 1)) ∈ K.Xset ↔ a = K.q i := by
  rw [mem_Xset, K.mem_XQ_head_p (i + 1) hi, mem_Hset]
  have h1 : K.p (i + 1) ≠ K.p 0 := fun h => by have := K.p_inj hi K.r_pos h; lia
  have h2 : K.p (i + 1) ≠ K.q 0 := K.p_ne_q hi K.r_pos
  simp only [h1, h2, false_and, or_false, Nat.add_sub_cancel]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨by lia, h⟩

theorem mem_X_head_q_succ (i : ℕ) (hi : i + 1 < K.r) (a : Fin n) :
    (a, K.q (i + 1)) ∈ K.Xset ↔ a = K.p (i + 1) := by
  rw [mem_Xset, K.mem_XQ_head_q (i + 1) hi, mem_Hset]
  have h1 : K.q (i + 1) ≠ K.p 0 := fun h => K.p_ne_q K.r_pos hi h.symm
  have h2 : K.q (i + 1) ≠ K.q 0 := fun h => by have := K.q_inj hi K.r_pos h; lia
  simp only [h1, h2, false_and, or_false]

theorem mem_X_head_p0 (a : Fin n) :
    (a, K.p 0) ∈ K.Xset ↔ a = K.p (K.r - 1) ∨ a = K.q (K.r - 1) := by
  rw [mem_Xset, K.mem_XQ_head_p 0 K.r_pos, mem_Hset]
  simp only [K.p0_ne_q0, false_and, or_false, true_and]
  constructor
  · rintro (⟨h, _⟩ | h)
    · lia
    · exact h
  · intro h; exact Or.inr h

theorem mem_X_head_q0 (a : Fin n) :
    (a, K.q 0) ∈ K.Xset ↔ a = K.p 0 ∨ a = K.q (K.r - 1) := by
  rw [mem_Xset, K.mem_XQ_head_q 0 K.r_pos, mem_Hset]
  simp only [(Ne.symm K.p0_ne_q0), false_and, false_or, true_and]

/-! Exterior boundary facts. -/

theorem boundary_eq_Q {w h : ℤ} {j : ℕ} (hj : j < K.r)
    (hb : D.boundary w = K.P j + 1 + (n : ℤ) * h) :
    j + 1 < K.r ∧ w = K.P (j + 1) + 1 + (n : ℤ) * h := by
  have hb' : D.boundary (w + (n : ℤ) * (-h)) = K.P j + 1 := by
    rw [D.boundary_add_period, hb]; ring
  by_cases hjr : j + 1 < K.r
  · refine ⟨hjr, ?_⟩
    have hZ : D.boundary (K.P (j + 1) + 1) = K.P j + 1 := K.bQ j hjr
    have hZ1 : D.boundary (K.P (j + 1) + 1 - 1) = K.P j := by
      rw [show K.P (j + 1) + 1 - 1 = K.P (j + 1) by ring]; exact K.bP j hjr
    have hZs : D.boundary (K.P (j + 1) + 1) < D.boundary (K.P (j + 1) + 1 + 1) :=
      D.strictAt_boundary_lt (K.strictQ (j + 1) hjr)
    have hw : w + (n : ℤ) * (-h) = K.P (j + 1) + 1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := D.boundary_monotone (show w + (n : ℤ) * (-h) ≤ K.P (j + 1) + 1 - 1 by lia)
        lia
      · have := D.boundary_monotone (show K.P (j + 1) + 1 + 1 ≤ w + (n : ℤ) * (-h) by lia)
        lia
    linarith
  · exfalso
    have hjr' : j = K.r - 1 := by lia
    subst hjr'
    apply D.no_boundary_gap K.t (D.boundary K.t) rfl K.gap_t (w + (n : ℤ) * (-h))
    rw [hb', K.bt]

theorem ext_bsub1_not_mem_L (v : ℤ) (hv : ∀ j < K.r, D.residue v ≠ K.p j ∧ D.residue v ≠ K.q j) :
    D.boundary v - 1 ∉ K.L := by
  rw [sub_one_mem_L_iff]
  rintro ⟨j, hj, hres⟩
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period hres
  obtain ⟨hj1, hw⟩ := K.boundary_eq_Q hj hk
  apply (hv (j + 1) hj1).2
  rw [hw, D.residue_add_period]; rfl

theorem sub1_not_mem_L_ext (v : ℤ) (hv : ∀ j < K.r, D.residue v ≠ K.p j ∧ D.residue v ≠ K.q j) :
    v - 1 ∉ K.L := by
  rw [sub_one_mem_L_iff]
  rintro ⟨j, hj, hres⟩
  exact (hv j hj).2 hres

theorem not_mem_L_ext (v : ℤ) (hv : ∀ j < K.r, D.residue v ≠ K.p j ∧ D.residue v ≠ K.q j) :
    v ∉ K.L := by
  rintro ⟨j, hj, hres⟩
  exact (hv j hj).1 hres

theorem σ_ext (v : ℤ) (hv : ∀ j < K.r, D.residue v ≠ K.p j ∧ D.residue v ≠ K.q j) :
    K.σ v = v := K.σ_of_not (K.not_mem_L_ext v hv) (K.sub1_not_mem_L_ext v hv)

theorem ext_strict_b_not_mem_L (v : ℤ)
    (hv : ∀ j < K.r, D.residue v ≠ K.p j ∧ D.residue v ≠ K.q j) (hs : D.strictAt v) :
    D.boundary v ∉ K.L := by
  rintro ⟨j, hj, hres⟩
  obtain ⟨e, he, heh, het⟩ := D.strictAt_edge hs
  by_cases hjr : j + 1 < K.r
  · obtain ⟨e', he', heh', het'⟩ := D.strictAt_edge (K.strictP (j + 1) (by lia) hjr)
    rw [K.bP j hjr] at het'
    have := D.strict_edge_eq_of_tail_eq he he' (by rw [het, het', hres]; rfl)
    subst this
    exact (hv (j + 1) hjr).1 (heh.symm.trans heh')
  · have hjr' : j = K.r - 1 := by lia
    subst hjr'
    have := D.strict_edge_eq_of_tail_eq he K.root_mem (by rw [het, K.root_tail, hres])
    subst this
    exact (hv 0 K.r_pos).2 (heh.symm.trans K.root_head_eq_q0)

theorem classify (v : ℤ) :
    (∃ j < K.r, ∃ h : ℤ, v = K.P j + (n : ℤ) * h) ∨
      (∃ j < K.r, ∃ h : ℤ, v = K.P j + 1 + (n : ℤ) * h) ∨
      (∀ j < K.r, D.residue v ≠ K.p j ∧ D.residue v ≠ K.q j) := by
  by_cases h1 : ∃ j < K.r, D.residue v = K.p j
  · obtain ⟨j, hj, h⟩ := h1
    obtain ⟨k, hk⟩ := D.residue_eq_exists_period h
    exact Or.inl ⟨j, hj, k, hk⟩
  by_cases h2 : ∃ j < K.r, D.residue v = K.q j
  · obtain ⟨j, hj, h⟩ := h2
    obtain ⟨k, hk⟩ := D.residue_eq_exists_period h
    exact Or.inr (Or.inl ⟨j, hj, k, hk⟩)
  push Not at h1 h2
  exact Or.inr (Or.inr fun j hj => ⟨h1 j hj, h2 j hj⟩)

theorem window_res_iff {lo hi a w : ℤ} (hw : hi - lo < n) (ha : lo ≤ a) (ha' : a ≤ hi)
    (hw1 : lo ≤ w) (hw2 : w ≤ hi) : D.residue w = D.residue a ↔ w = a :=
  ⟨D.residue_eq_of_window hw1 hw2 ha ha' hw, fun h => by rw [h]⟩

theorem P_window (i : ℕ) (hi : i + 1 < K.r) : K.P (i + 1) - K.P i < n := by
  have := AliasContacts.window_lt (D := D) (K.P (i + 1)); rw [K.bP i hi] at this; exact this

theorem β_window : K.P 0 + 1 - K.β < n := by
  have := AliasContacts.window_lt (D := D) (K.P 0 + 1); rw [K.b0] at this; exact this

end AliasContacts

end VerticalStripLLT.Circular
