import VerticalStripLLT.Circular.AliasReductionExceptions

set_option backward.isDefEq.respectTransparency false

/-! The simultaneous swap conjugates the lifted strict relations and the lifted
non-exceptional edge relations of the source and the alias target. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace AliasContacts

variable {n : ℕ} {D : Diagram n} (K : AliasContacts D)

theorem q_succ_ne_p0 (i : ℕ) (hi : i + 1 < K.r) : D.residue (K.P (i + 1) + 1) ≠ K.p 0 :=
  fun h => K.p_ne_q K.r_pos hi h.symm

theorem q_succ_ne_q0 (i : ℕ) (hi : i + 1 < K.r) : D.residue (K.P (i + 1) + 1) ≠ K.q 0 :=
  fun h => by have := K.q_inj hi K.r_pos h; lia

theorem p_succ_ne_p0 (i : ℕ) (hi : i + 1 < K.r) : D.residue (K.P (i + 1)) ≠ K.p 0 :=
  fun h => by have := K.p_inj hi K.r_pos h; lia

theorem p_succ_ne_q0 (i : ℕ) (hi : i + 1 < K.r) : D.residue (K.P (i + 1)) ≠ K.q 0 :=
  K.p_ne_q hi K.r_pos

/-! Non-exceptional edge lifts. -/

theorem M2P_succ (i : ℕ) (hi : i + 1 < K.r) (u : ℤ) :
    (D.boundary (K.P (i + 1)) ≤ u ∧ u < K.P (i + 1) ∧ (D.residue u, K.p (i + 1)) ∉ K.Xset) ↔
    (K.target.boundary (K.P (i + 1) + 1) ≤ K.σ u ∧ K.σ u < K.P (i + 1) + 1 ∧
      (D.residue (K.σ u), K.q (i + 1)) ∉ K.XQset) := by
  rw [K.bP i hi, K.mem_X_head_p_succ i hi, K.target_boundary_other (K.q_succ_ne_p0 i hi)
    (K.q_succ_ne_q0 i hi), K.bQ i hi, K.mem_XQ_head_q (i + 1) hi]
  have hw := K.P_window i hi
  have h2 := K.P_add_two_le i hi
  have hS := K.S2 (K.P_mem_L i (by lia)) (K.P_sub_one_not_mem_L (i + 1) hi) (by lia) u
  constructor
  · rintro ⟨a, b, c⟩
    have hne : u ≠ K.P i + 1 := fun h => c (by rw [h]; rfl)
    obtain ⟨a', b'⟩ := hS.mp ⟨a, b, hne⟩
    refine ⟨a', by lia, ?_⟩
    intro hres
    have := D.residue_eq_of_window (lo := K.P i + 1) (hi := K.P (i + 1) + 1) a' (by lia)
      (by lia) (by lia) (by lia) hres
    lia
  · rintro ⟨a, b, c⟩
    have hne : K.σ u ≠ K.P (i + 1) := fun h => c (by rw [h]; rfl)
    obtain ⟨a', b', c'⟩ := hS.mpr ⟨a, by lia⟩
    refine ⟨a', b', ?_⟩
    intro hres
    exact c' (D.residue_eq_of_window (lo := K.P i) (hi := K.P (i + 1)) a' (by lia)
      (by lia) (by lia) hw hres)

theorem M2P_zero (u : ℤ) :
    (D.boundary (K.P 0) ≤ u ∧ u < K.P 0 ∧ (D.residue u, K.p 0) ∉ K.Xset) ↔
    (K.target.boundary (K.P 0 + 1) ≤ K.σ u ∧ K.σ u < K.P 0 + 1 ∧
      (D.residue (K.σ u), K.q 0) ∉ K.XQset) := by
  have hβ : K.β = D.boundary (K.P 0) := rfl
  rw [K.mem_X_head_p0, K.target_boundary_q0 rfl, K.b0, K.mem_XQ_head_q 0 K.r_pos, ← hβ]
  have hw := K.β_window
  have h2 := K.β_add_two_le
  have hS := K.S1 K.β_mem_L (K.P_sub_one_not_mem_L 0 K.r_pos) u
  have r1 := K.res_β
  have r2 := K.res_β1
  constructor
  · rintro ⟨a, b, c⟩
    have hne1 : u ≠ K.β := fun h => c (Or.inl (by rw [h, r1]; rfl))
    have hne2 : u ≠ K.β + 1 := fun h => c (Or.inr (by rw [h, r2]; rfl))
    obtain ⟨a', b'⟩ := hS.mp ⟨by lia, b⟩
    refine ⟨a', by lia, ?_⟩
    intro hres
    have := D.residue_eq_of_window (lo := K.β) (hi := K.P 0 + 1) (by lia) (by lia)
      (by lia) (by lia) hw hres
    lia
  · rintro ⟨a, b, c⟩
    have hne : K.σ u ≠ K.P 0 := fun h => c (by rw [h]; rfl)
    obtain ⟨a', b'⟩ := hS.mpr ⟨a, by lia⟩
    refine ⟨by lia, b', ?_⟩
    rintro (hres | hres)
    · have := D.residue_eq_of_window (lo := K.β) (hi := K.P 0 + 1) (by lia) (by lia)
        (le_refl _) (by lia) hw (hres.trans r1.symm)
      lia
    · have := D.residue_eq_of_window (lo := K.β) (hi := K.P 0 + 1) (by lia) (by lia)
        (by lia) (by lia) hw (hres.trans r2.symm)
      lia

theorem M2Q_succ (i : ℕ) (hi : i + 1 < K.r) (u : ℤ) :
    (D.boundary (K.P (i + 1) + 1) ≤ u ∧ u < K.P (i + 1) + 1 ∧
      (D.residue u, K.q (i + 1)) ∉ K.Xset) ↔
    (K.target.boundary (K.P (i + 1)) ≤ K.σ u ∧ K.σ u < K.P (i + 1) ∧
      (D.residue (K.σ u), K.p (i + 1)) ∉ K.XQset) := by
  rw [K.bQ i hi, K.mem_X_head_q_succ i hi, K.target_boundary_other (K.p_succ_ne_p0 i hi)
    (K.p_succ_ne_q0 i hi), K.bP i hi, K.mem_XQ_head_p (i + 1) hi]
  simp only [Nat.add_sub_cancel, le_add_iff_nonneg_left, zero_le, true_and]
  have hw := K.P_window i hi
  have h2 := K.P_add_two_le i hi
  have hS := K.S2 (K.P_mem_L i (by lia)) (K.P_sub_one_not_mem_L (i + 1) hi) (by lia)
    (K.σ u)
  rw [K.σ_σ] at hS
  constructor
  · rintro ⟨a, b, c⟩
    have hne : u ≠ K.P (i + 1) := fun h => c (by rw [h]; rfl)
    obtain ⟨a', b', c'⟩ := hS.mpr ⟨a, by lia⟩
    refine ⟨a', b', ?_⟩
    intro hres
    exact c' (D.residue_eq_of_window (lo := K.P i) (hi := K.P (i + 1)) a' (by lia)
      (by lia) (by lia) hw hres)
  · rintro ⟨a, b, c⟩
    have hne : K.σ u ≠ K.P i + 1 := fun h => c (by rw [h]; rfl)
    obtain ⟨a', b'⟩ := hS.mp ⟨a, b, hne⟩
    refine ⟨a', by lia, ?_⟩
    intro hres
    have := D.residue_eq_of_window (lo := K.P i + 1) (hi := K.P (i + 1) + 1) a' (by lia)
      (by lia) (by lia) (by lia) hres
    lia

theorem M2Q_zero (u : ℤ) :
    (D.boundary (K.P 0 + 1) ≤ u ∧ u < K.P 0 + 1 ∧ (D.residue u, K.q 0) ∉ K.Xset) ↔
    (K.target.boundary (K.P 0) ≤ K.σ u ∧ K.σ u < K.P 0 ∧
      (D.residue (K.σ u), K.p 0) ∉ K.XQset) := by
  have hβ : K.β = D.boundary (K.P 0) := rfl
  rw [K.b0, K.mem_X_head_q0, K.target_boundary_p0 rfl, K.mem_XQ_head_p 0 K.r_pos, ← hβ]
  simp only [Nat.le_zero, one_ne_zero, false_and, not_false_eq_true, and_true]
  have hw := K.β_window
  have h2 := K.β_add_two_le
  have hS := K.S2 K.β_mem_L (K.P_sub_one_not_mem_L 0 K.r_pos) (by lia) u
  have r2 := K.res_β1
  constructor
  · rintro ⟨a, b, c⟩
    have hne1 : u ≠ K.P 0 := fun h => c (Or.inl (by rw [h]; rfl))
    have hne2 : u ≠ K.β + 1 := fun h => c (Or.inr (by rw [h, r2]; rfl))
    exact hS.mp ⟨a, by lia, hne2⟩
  · rintro ⟨a, b⟩
    obtain ⟨a', b', c'⟩ := hS.mpr ⟨a, b⟩
    refine ⟨a', by lia, ?_⟩
    rintro (hres | hres)
    · have := D.residue_eq_of_window (lo := K.β) (hi := K.P 0 + 1) a' (by lia)
        (by lia) (by lia) hw hres
      lia
    · exact c' (D.residue_eq_of_window (lo := K.β) (hi := K.P 0 + 1) a' (by lia)
        (by lia) (by lia) hw (hres.trans r2.symm))

theorem M2E (v : ℤ) (hv : ∀ j < K.r, D.residue v ≠ K.p j ∧ D.residue v ≠ K.q j) (u : ℤ) :
    (D.boundary v ≤ u ∧ u < v ∧ (D.residue u, D.residue v) ∉ K.Xset) ↔
    (K.target.boundary v ≤ K.σ u ∧ K.σ u < v ∧ (D.residue (K.σ u), D.residue v) ∉ K.XQset) := by
  have h1 := K.not_mem_X_ext _ hv (D.residue u)
  have h2 := K.not_mem_XQ_ext _ hv (D.residue (K.σ u))
  rw [K.target_boundary_other (hv 0 K.r_pos).1 (hv 0 K.r_pos).2]
  have t1 := K.threshold (K.ext_bsub1_not_mem_L v hv) u
  have t2 := K.threshold (K.sub1_not_mem_L_ext v hv) u
  constructor
  · rintro ⟨a, b, _⟩
    exact ⟨t1.mp a, lt_of_not_ge fun h => (not_le.mpr b) (t2.mpr h), h2⟩
  · rintro ⟨a, b, _⟩
    exact ⟨t1.mpr a, lt_of_not_ge fun h => (not_le.mpr b) (t2.mp h), h1⟩

/-- Non-exceptional edge lifts are conjugated by the simultaneous swap. -/
theorem exterior_lift_conjugacy (u v : ℤ) :
    (D.boundary v ≤ u ∧ u < v ∧ (D.residue u, D.residue v) ∉ K.Xset) ↔
    (K.target.boundary (K.σ v) ≤ K.σ u ∧ K.σ u < K.σ v ∧
      (D.residue (K.σ u), D.residue (K.σ v)) ∉ K.XQset) := by
  rcases K.classify v with ⟨j, hj, h, rfl⟩ | ⟨j, hj, h, rfl⟩ | hv
  · obtain ⟨u', rfl⟩ : ∃ u', u = u' + (n : ℤ) * h := ⟨u - (n : ℤ) * h, by ring⟩
    simp only [D.boundary_add_period, D.residue_add_period, K.σ_translate, K.σ_P j hj,
      K.target_boundary_add_period, add_le_add_iff_right, add_lt_add_iff_right]
    rcases j with _ | i
    · exact K.M2P_zero u'
    · exact K.M2P_succ i hj u'
  · obtain ⟨u', rfl⟩ : ∃ u', u = u' + (n : ℤ) * h := ⟨u - (n : ℤ) * h, by ring⟩
    simp only [D.boundary_add_period, D.residue_add_period, K.σ_translate, K.σ_P1 j hj,
      K.target_boundary_add_period, add_le_add_iff_right, add_lt_add_iff_right]
    rcases j with _ | i
    · exact K.M2Q_zero u'
    · exact K.M2Q_succ i hj u'
  · rw [K.σ_ext v hv]
    exact K.M2E v hv u

/-! Strict lifts. -/

theorem M1P_succ (i : ℕ) (hi : i + 1 < K.r) (u : ℤ) :
    (D.strictAt (K.P (i + 1)) ∧ u = D.boundary (K.P (i + 1))) ↔
    (K.target.strictAt (K.P (i + 1) + 1) ∧ K.σ u = K.target.boundary (K.P (i + 1) + 1)) := by
  rw [K.bP i hi, K.target_boundary_other (K.q_succ_ne_p0 i hi) (K.q_succ_ne_q0 i hi),
    K.bQ i hi, K.target_strictAt_iff]
  have hs1 := K.strictP (i + 1) (by lia) hi
  have hs2 := K.strictQ (i + 1) hi
  rw [K.σ_eq_iff, K.σ_P1 i (by lia)]
  simp only [hs1, true_and, hs2, K.q_succ_ne_q0 i hi, ne_eq, not_false_eq_true, and_self,
    or_true]

theorem M1P_zero (u : ℤ) :
    (D.strictAt (K.P 0) ∧ u = D.boundary (K.P 0)) ↔
    (K.target.strictAt (K.P 0 + 1) ∧ K.σ u = K.target.boundary (K.P 0 + 1)) := by
  rw [K.target_strictAt_iff]
  have h0 : D.residue (K.P 0 + 1) = K.q 0 := rfl
  simp only [K.notStrict0, false_and, h0, (Ne.symm K.p0_ne_q0), ne_eq, not_true_eq_false,
    and_false, or_self]

theorem M1Q_succ (i : ℕ) (hi : i + 1 < K.r) (u : ℤ) :
    (D.strictAt (K.P (i + 1) + 1) ∧ u = D.boundary (K.P (i + 1) + 1)) ↔
    (K.target.strictAt (K.P (i + 1)) ∧ K.σ u = K.target.boundary (K.P (i + 1))) := by
  rw [K.bQ i hi, K.target_boundary_other (K.p_succ_ne_p0 i hi) (K.p_succ_ne_q0 i hi),
    K.bP i hi, K.target_strictAt_iff]
  have hs1 := K.strictP (i + 1) (by lia) hi
  have hs2 := K.strictQ (i + 1) hi
  rw [K.σ_eq_iff, K.σ_P i (by lia)]
  simp only [hs1, true_and, hs2, K.p_succ_ne_q0 i hi, ne_eq, not_false_eq_true, and_self,
    or_true]

theorem M1Q_zero (u : ℤ) :
    (D.strictAt (K.P 0 + 1) ∧ u = D.boundary (K.P 0 + 1)) ↔
    (K.target.strictAt (K.P 0) ∧ K.σ u = K.target.boundary (K.P 0)) := by
  have hβ : K.β = D.boundary (K.P 0) := rfl
  rw [K.b0, K.target_boundary_p0 rfl, K.target_strictAt_iff, ← hβ, K.σ_eq_iff, K.σ_β1]
  have h0 : D.residue (K.P 0) = K.p 0 := rfl
  simp only [K.strictQ 0 K.r_pos, true_and, h0, true_or]

theorem M1E (v : ℤ) (hv : ∀ j < K.r, D.residue v ≠ K.p j ∧ D.residue v ≠ K.q j) (u : ℤ) :
    (D.strictAt v ∧ u = D.boundary v) ↔
    (K.target.strictAt v ∧ K.σ u = K.target.boundary v) := by
  rw [K.target_boundary_other (hv 0 K.r_pos).1 (hv 0 K.r_pos).2, K.target_strictAt_iff]
  simp only [(hv 0 K.r_pos).1, (hv 0 K.r_pos).2, ne_eq, not_false_eq_true, and_true,
    false_or]
  constructor
  · rintro ⟨hs, rfl⟩
    exact ⟨hs, K.σ_of_not (K.ext_strict_b_not_mem_L v hv hs) (K.ext_bsub1_not_mem_L v hv)⟩
  · rintro ⟨hs, h⟩
    refine ⟨hs, ?_⟩
    rw [K.σ_eq_iff, K.σ_of_not (K.ext_strict_b_not_mem_L v hv hs)
      (K.ext_bsub1_not_mem_L v hv)] at h
    exact h

/-- Strict lifts are conjugated by the simultaneous swap. -/
theorem strict_lift_conjugacy (u v : ℤ) :
    (D.strictAt v ∧ u = D.boundary v) ↔
    (K.target.strictAt (K.σ v) ∧ K.σ u = K.target.boundary (K.σ v)) := by
  rcases K.classify v with ⟨j, hj, h, rfl⟩ | ⟨j, hj, h, rfl⟩ | hv
  · obtain ⟨u', rfl⟩ : ∃ u', u = u' + (n : ℤ) * h := ⟨u - (n : ℤ) * h, by ring⟩
    simp only [D.boundary_add_period, D.strictAt_add_period, K.target.strictAt_add_period,
      K.σ_translate, K.σ_P j hj, K.target_boundary_add_period, add_left_inj]
    rcases j with _ | i
    · exact K.M1P_zero u'
    · exact K.M1P_succ i hj u'
  · obtain ⟨u', rfl⟩ : ∃ u', u = u' + (n : ℤ) * h := ⟨u - (n : ℤ) * h, by ring⟩
    simp only [D.boundary_add_period, D.strictAt_add_period, K.target.strictAt_add_period,
      K.σ_translate, K.σ_P1 j hj, K.target_boundary_add_period, add_left_inj]
    rcases j with _ | i
    · exact K.M1Q_zero u'
    · exact K.M1Q_succ i hj u'
  · rw [K.σ_ext v hv]
    exact K.M1E v hv u

end AliasContacts

end VerticalStripLLT.Circular
