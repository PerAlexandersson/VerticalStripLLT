import VerticalStripLLT.Circular.ChainSingletonAscentCount
import VerticalStripLLT.Circular.InsertionColorings
import Mathlib.Tactic.FinCases

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace VerticalStripLLT.Circular.ChainSingletonInsert

theorem insertNth_eq_ite {α : Type*} {k : ℕ} (j : Fin (k + 2)) (z : α) (c : Fin (k + 1) → α)
    (t : Fin (k + 2)) :
    (j.insertNth (α := fun _ => α) z c) t =
      if h : t.val < j.val then c ⟨t.val, by lia⟩ else
        if t = j then z else c ⟨t.val - 1, by lia⟩ := by
  rcases lt_trichotomy t j with h | h | h
  · rw [Fin.insertNth_apply_below h, dite_eq_left (Fin.lt_def.mp h), eq_rec_constant]
    rfl
  · subst h
    simp
  · rw [Fin.insertNth_apply_above h, dite_eq_right (by have := Fin.lt_def.mp h; lia),
      ite_eq_right (ne_of_gt h), eq_rec_constant]
    rfl

theorem strictMono_insertNth_iff {m k : ℕ} (c : Fin (k + 1) → Fin m) (hc : StrictMono c)
    (z : Fin m) (j : Fin (k + 2)) :
    StrictMono (j.insertNth (α := fun _ => Fin m) z c) ↔
      (∀ h : 0 < j.val, c ⟨j.val - 1, by lia⟩ < z) ∧
        (∀ h : j.val < k + 1, z < c ⟨j.val, h⟩) := by
  rw [Fin.strictMono_iff_lt_succ]
  simp only [insertNth_eq_ite]
  constructor
  · intro H
    constructor
    · intro h0
      have := H ⟨j.val - 1, by lia⟩
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      rw [dite_eq_left (by lia), dite_eq_right (by lia), ite_eq_left (by ext; simp; lia)] at this
      exact this
    · intro hj
      have := H ⟨j.val, hj⟩
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      rw [dite_eq_right (by lia), ite_eq_left (by ext; simp), dite_eq_right (by lia),
        ite_eq_right (by intro h; have := congrArg Fin.val h; simp at this)] at this
      simpa using this
  · rintro ⟨H1, H2⟩ t
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases h1 : t.val + 1 < j.val
    · rw [dite_eq_left (by lia), dite_eq_left h1]
      exact hc (Fin.lt_def.mpr (by simp))
    by_cases h2 : t.val + 1 = j.val
    · rw [dite_eq_left (by lia), dite_eq_right (by lia), ite_eq_left (by ext; simp; lia)]
      have := H1 (by lia)
      convert this using 2
      ext; simp; lia
    by_cases h3 : t.val = j.val
    · rw [dite_eq_right (by lia), ite_eq_left (by ext; simp; lia), dite_eq_right (by lia),
        ite_eq_right (by intro h; have := congrArg Fin.val h; simp at this; lia)]
      have := H2 (by lia)
      convert this using 2
      ext; simp; lia
    · have hne1 : t.castSucc ≠ j := by
        intro h; have := congrArg Fin.val h; rw [Fin.val_castSucc] at this; lia
      have hne2 : t.succ ≠ j := by
        intro h; have := congrArg Fin.val h; rw [Fin.val_succ] at this; lia
      rw [dite_eq_right (by lia), ite_eq_right hne1, dite_eq_right (by lia), ite_eq_right hne2]
      exact hc (Fin.lt_def.mpr (by simp only; lia))

theorem strictMono_of_insertNth {m k : ℕ} (c : Fin (k + 1) → Fin m) (z : Fin m)
    (j : Fin (k + 2)) (h : StrictMono (j.insertNth (α := fun _ => Fin m) z c)) :
    StrictMono c := by
  have e : c = (j.insertNth (α := fun _ => Fin m) z c) ∘ j.succAbove := by
    funext i
    simp [Fin.insertNth_apply_succAbove]
  rw [e]
  exact h.comp (Fin.strictMono_succAbove j)

theorem insertNth_unique {m k : ℕ} (c : Fin (k + 1) → Fin m) (hc : StrictMono c)
    (z : Fin m) (j j' : Fin (k + 2))
    (h : StrictMono (j.insertNth (α := fun _ => Fin m) z c))
    (h' : StrictMono (j'.insertNth (α := fun _ => Fin m) z c)) : j = j' := by
  rw [strictMono_insertNth_iff c hc] at h h'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hl := Fin.lt_def.mp hlt
    have a1 := h.2 (by lia)
    have a2 := h'.1 (by lia)
    have a3 : c ⟨j.val, by lia⟩ ≤ c ⟨j'.val - 1, by lia⟩ :=
      hc.monotone (Fin.le_def.mpr (by simp only; lia))
    exact absurd (lt_trans a2 (lt_of_lt_of_le a1 a3)) (lt_irrefl _)
  · have hl := Fin.lt_def.mp hlt
    have a1 := h'.2 (by lia)
    have a2 := h.1 (by lia)
    have a3 : c ⟨j'.val, by lia⟩ ≤ c ⟨j.val - 1, by lia⟩ :=
      hc.monotone (Fin.le_def.mpr (by simp only; lia))
    exact absurd (lt_trans a2 (lt_of_lt_of_le a1 a3)) (lt_irrefl _)

theorem pow_sum_indicator_of_unique {R ι : Type*} [CommSemiring R] [Fintype ι]
    (P : ι → Prop) [DecidablePred P] (hP : ∀ i j, P i → P j → i = j) (q : R) :
    (1 + q) ^ (∑ i, if P i then 1 else 0) = 1 + ∑ i, if P i then q else 0 := by
  by_cases hex : ∃ i, P i
  · obtain ⟨i, hi⟩ := hex
    have h1 : (∑ j, if P j then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j _ hj
        simp [show ¬ P j from fun hj' => hj (hP j i hj' hi)]
      · simp
    have h2 : (∑ j, if P j then q else 0) = q := by
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j _ hj
        simp [show ¬ P j from fun hj' => hj (hP j i hj' hi)]
      · simp
    rw [h1, h2, pow_one]
  · push Not at hex
    simp [hex]

end VerticalStripLLT.Circular.ChainSingletonInsert

namespace VerticalStripLLT.Circular.ChainSingletonData

open ChainSingletonInsert

variable {n k : ℕ} {D : Diagram n} (S : ChainSingletonData D k)

/-- The insertion-gap incidence list `(b_1, a_1, ..., a_L)`. -/
def gapEps (j : Fin (k + 2)) : Prop :=
  if j.val = 0 then S.incoming 0 else S.outgoing ⟨j.val - 1, by lia⟩

theorem gaps_eq_sum {m : ℕ} (c : Fin (k + 1) → Fin m) (hc : StrictMono c) (z : Fin m) :
    (if S.incoming 0 ∧ z < c 0 then 1 else 0) +
      (if S.outgoing (Fin.last k) ∧ c (Fin.last k) < z then 1 else 0) +
      (∑ i : Fin k, if S.outgoing i.castSucc ∧ c i.castSucc < z ∧ z < c i.succ then 1 else 0) =
    ∑ j : Fin (k + 2),
      if S.gapEps j ∧ StrictMono (j.insertNth (α := fun _ => Fin m) z c) then 1 else 0 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have t0 : (if S.gapEps 0 ∧ StrictMono ((0 : Fin (k + 2)).insertNth (α := fun _ => Fin m) z c)
      then 1 else 0) = (if S.incoming 0 ∧ z < c 0 then 1 else 0) := by
    apply if_congr _ rfl rfl
    rw [strictMono_insertNth_iff c hc]
    simp only [gapEps, Fin.val_zero, ite_true, lt_irrefl, IsEmpty.forall_iff, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 (by lia)⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun _ => h2⟩
  have tl : (if S.gapEps (Fin.last k).succ ∧
      StrictMono ((Fin.last k).succ.insertNth (α := fun _ => Fin m) z c) then 1 else 0) =
      (if S.outgoing (Fin.last k) ∧ c (Fin.last k) < z then 1 else 0) := by
    apply if_congr _ rfl rfl
    rw [strictMono_insertNth_iff c hc]
    simp only [gapEps, Fin.val_succ, Fin.val_last, Nat.add_sub_cancel]
    rw [ite_eq_right (by lia)]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2 (by lia)⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun _ => h2, fun h => absurd h (by lia)⟩
  have ti : ∀ i : Fin k, (if S.gapEps i.castSucc.succ ∧
      StrictMono (i.castSucc.succ.insertNth (α := fun _ => Fin m) z c) then 1 else 0) =
      (if S.outgoing i.castSucc ∧ c i.castSucc < z ∧ z < c i.succ then 1 else 0) := by
    intro i
    apply if_congr _ rfl rfl
    rw [strictMono_insertNth_iff c hc]
    simp only [gapEps, Fin.val_succ, Fin.val_castSucc, Nat.add_sub_cancel]
    rw [ite_eq_right (by lia)]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2 (by lia), h3 (by lia)⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, fun _ => h2, fun _ => h3⟩
  rw [t0, tl, Finset.sum_congr rfl (fun i _ => ti i)]
  ring

theorem xQShift_X_prod {m : ℕ} (z : Fin m) (c : Fin (k + 1) → Fin m) :
    xQShift m (MvPolynomial.X z * ∏ i, MvPolynomial.X (c i)) =
      MvPolynomial.X z * ∏ i, MvPolynomial.X (c i) := by
  simp [xQShift]

/-- The coloring side in closed form, before identifying the gap count. -/
theorem xQShift_coloringLLT_closed (m : ℕ) :
    xQShift m (D.coloringLLT m) =
      MvPolynomial.C ((Polynomial.X + 1) ^ S.baseAscentCount) *
        (MvPolynomial.esymm (Fin m) Q 1 * MvPolynomial.esymm (Fin m) Q (k + 1) +
          (∑ j : Fin (k + 2), if S.gapEps j then MvPolynomial.C Polynomial.X else 0) *
            MvPolynomial.esymm (Fin m) Q (k + 1 + 1)) := by
  rw [← isolated_with_insertion_correction_sum (k + 1) m
    (fun j => if S.gapEps j then MvPolynomial.C Polynomial.X else 0)]
  rw [S.coloringLLT_reindex m, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : StrictMono c
  · rw [ite_eq_left hc, ite_eq_left hc, map_mul, xQShift_C_X_pow', xQShift_X_prod]
    have hc' : StrictMono (fun i => ((S.coloringEquiv m).symm (z, c)) (S.chain i)) := by
      simpa only [coloringEquiv_symm_chain] using hc
    rw [S.ascentCount_eq_base_add_gaps _ hc']
    simp only [coloringEquiv_symm_chain, coloringEquiv_symm_isolated]
    simp only [add_assoc]
    rw [← add_assoc (if S.incoming 0 ∧ z < c 0 then 1 else 0), S.gaps_eq_sum c hc z, pow_add,
      add_comm Polynomial.X 1,
      pow_sum_indicator_of_unique _ (fun i j hi hj => insertNth_unique c hc z i j hi.2 hj.2),
      MvPolynomial.C_mul, mul_assoc]
    congr 1
    rw [map_add, map_one, add_mul, one_mul, map_sum, Finset.sum_mul]
    apply congrArg (fun p : XPoly m =>
      (MvPolynomial.X z * ∏ i, MvPolynomial.X (c i)) + p)
    apply Finset.sum_congr rfl
    intro j _
    by_cases h1 : S.gapEps j <;> by_cases h2 : StrictMono (j.insertNth (α := fun _ => Fin m) z c)
    all_goals simp [h1, h2]
  · rw [ite_eq_right hc, ite_eq_right hc, map_zero, zero_add]
    symm
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right (fun h => hc (strictMono_of_insertNth c z j h)), mul_zero]

end VerticalStripLLT.Circular.ChainSingletonData
