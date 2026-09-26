import VerticalStripLLT.Circular.AliasReductionBasic
import VerticalStripLLT.Circular.AliasRealization
import VerticalStripLLT.Circular.WalkBound

set_option backward.isDefEq.respectTransparency false

/-! Integer contact data of the overlapping ND branch. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem boundary_succ_of_gap_zero_strict {z : ℤ} (hgap : D.eastGap z = 0)
    (hs : D.strictAt z) : D.boundary (z + 1) = D.boundary z + 1 := by
  unfold eastGap at hgap
  rw [ite_eq_left hs] at hgap
  lia

theorem boundary_succ_of_gap_zero_nonstrict {z : ℤ} (hgap : D.eastGap z = 0)
    (hs : ¬ D.strictAt z) : D.boundary (z + 1) = D.boundary z := by
  unfold eastGap at hgap
  rw [ite_eq_right hs] at hgap
  lia

theorem strictAt_edge {z : ℤ} (h : D.strictAt z) :
    ∃ e ∈ D.strict, e.head = D.residue z ∧ e.tail = D.residue (D.boundary z) := by
  obtain ⟨e, he, hh⟩ := h
  refine ⟨e, he, hh, D.residue_tail_of_length hh ?_⟩
  rw [(D.strict_corner e he).1, hh, boundary]
  ring

theorem ReverseBounce.exists_chain {t x : ℤ} (h : ReverseBounce D t x) :
    ∃ r : ℕ, ∃ P : ℕ → ℤ, 1 ≤ r ∧ P 0 = x ∧ P (r - 1) = D.boundary t ∧
      (∀ j, j + 1 < r → D.boundary (P (j + 1)) = P j) ∧
      (∀ j, 1 ≤ j → j < r → D.strictAt (P j) ∧ D.strictAt (P j + 1)) ∧
      (∀ j, j < r → D.eastGap (P j) = 0) := by
  induction h with
  | stop t hgap _ =>
    refine ⟨1, fun _ => D.boundary t, le_rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro j hj; lia
    · intro j h1 h2; lia
    · intro j _; exact hgap
  | @descend t x hgap hfirst hsecond _ ih =>
    obtain ⟨r, P, hr, h0, hlast, hb, hs, hg⟩ := ih
    refine ⟨r + 1, fun j => if j = r then D.boundary t else P j, by lia, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [show (0 : ℕ) ≠ r by lia, ite_false]; exact h0
    · simp
    · intro j hj
      by_cases hjr : j + 1 = r
      · simp only [hjr, ite_true, show j ≠ r by lia, ite_false]
        rw [← hlast]; congr 1; lia
      · simp only [hjr, ite_false, show j ≠ r by lia]
        exact hb j (by lia)
    · intro j h1 h2
      by_cases hjr : j = r
      · simp only [hjr, ite_true]; exact ⟨hfirst, hsecond⟩
      · simp only [hjr, ite_false]; exact hs j h1 (by lia)
    · intro j hj
      by_cases hjr : j = r
      · simp only [hjr, ite_true]; exact hgap
      · simp only [hjr, ite_false]; exact hg j (by lia)

end Diagram

/-- The lifted contact configuration of the overlapping ND branch. -/
structure AliasContacts {n : ℕ} (D : Diagram n) where
  r : ℕ
  P : ℕ → ℤ
  t : ℤ
  two_le : 2 ≤ r
  bP : ∀ j, j + 1 < r → D.boundary (P (j + 1)) = P j
  bQ : ∀ j, j + 1 < r → D.boundary (P (j + 1) + 1) = P j + 1
  strictP : ∀ j, 1 ≤ j → j < r → D.strictAt (P j)
  strictQ : ∀ j, j < r → D.strictAt (P j + 1)
  notStrict0 : ¬ D.strictAt (P 0)
  b0 : D.boundary (P 0 + 1) = D.boundary (P 0)
  strict_t : D.strictAt t
  bt : D.boundary t = P (r - 1)
  res_t : D.residue t = D.residue (P 0 + 1)
  gap_t : D.boundary t + 2 ≤ D.boundary (t + 1)
  area_t : 3 ≤ D.area.area (D.residue t)
  injP : ∀ i j, i < r → j < r → D.residue (P i) = D.residue (P j) → i = j
  injQ : ∀ i j, i < r → j < r → D.residue (P i + 1) = D.residue (P j + 1) → i = j
  nePQ : ∀ i j, i < r → j < r → D.residue (P i) ≠ D.residue (P j + 1)

namespace Diagram

variable {n : ℕ} (D : Diagram n)

private theorem walk_step_distinct (ha : D.edgeData.Admissible ∅) (r : ℕ) (hr : 1 ≤ r)
    (w : ℕ → Fin n) (hstep : ∀ i, i + 1 < 2 * r → D.edgeData.selected ∅ (w i) (w (i + 1)))
    (i j : ℕ) (hi : i < 2 * r) (hj : j < 2 * r) (h : w i = w j) : i = j := by
  obtain ⟨k, hk⟩ : ∃ k, 2 * r = k + 1 := ⟨2 * r - 1, by lia⟩
  let f : Fin (k + 1) → Fin n := fun a => w a.val
  have hinj := acyclic_walk_injective (D.edgeData.selected ∅) ha f (by
    intro a
    have := hstep a.val (by lia)
    simpa [f] using this)
  have := @hinj ⟨i, by lia⟩ ⟨j, by lia⟩ h
  simpa using congrArg Fin.val this

theorem aliasContacts_of_reverseBounce (ha : D.edgeData.Admissible ∅) {t x : ℤ}
    (ht : D.EligibleDE t) (h : ReverseBounce D t x)
    (hx : ¬ D.strictAt x) (hx1 : D.strictAt (x + 1))
    (halias : D.residue t = D.residue (x + 1)) :
    ∃ K : AliasContacts D, K.P 0 = x ∧ K.t = t := by
  obtain ⟨r, P, hr, h0, hlast, hb, hs, hg⟩ := ReverseBounce.exists_chain D h
  subst h0
  have hgap0 := hg 0 (by lia)
  have hb0 := D.boundary_succ_of_gap_zero_nonstrict hgap0 hx
  have hbQ : ∀ j, j + 1 < r → D.boundary (P (j + 1) + 1) = P j + 1 := by
    intro j hj
    rw [D.boundary_succ_of_gap_zero_strict (hg (j + 1) hj) (hs (j + 1) (by lia) hj).1,
      hb j hj]
  have harea3 := ht.alias_area_ge_three D h halias
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period halias
  have hbt : D.boundary t = D.boundary (P 0) + n * k := by
    rw [hk, D.boundary_add_period, hb0]
  have hstrictQ : ∀ j, j < r → D.strictAt (P j + 1) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact hx1
    · exact (hs j hjpos hj).2
  have hr2 : 2 ≤ r := by
    by_contra hr1
    have hr1 : r = 1 := by lia
    subst hr1
    simp only [Nat.sub_self] at hlast
    have hle := D.boundary_le_self (P 0)
    have hlt := D.self_sub_period_lt_boundary (P 0)
    have hn : (0 : ℤ) < n := by exact_mod_cast D.area.positive
    have hk0 : k = 0 := by
      have h1 : P 0 = D.boundary (P 0) + n * k := hlast.trans hbt
      have h2 : 0 ≤ (n : ℤ) * k := by lia
      have h3 : (n : ℤ) * k < n := by lia
      rcases lt_trichotomy k 0 with hk' | hk' | hk'
      · nlinarith
      · exact hk'
      · nlinarith
    subst hk0
    have htb : D.boundary t = t - 1 := by rw [← hlast]; rw [hk]; ring
    have : (D.area.area (D.residue t) : ℤ) = 1 := by
      rw [Diagram.boundary] at htb; lia
    lia
  -- the strict walk
  let w : ℕ → Fin n := fun i => if i < r then D.residue (P i) else D.residue (P (i - r) + 1)
  have hstep : ∀ i, i + 1 < 2 * r → D.edgeData.selected ∅ (w i) (w (i + 1)) := by
    intro i hi
    by_cases hir : i + 1 < r
    · have hsel := D.selected_of_strictAt (hs (i + 1) (by lia) hir).1
      rw [hb i hir] at hsel
      simpa [w, hir, show i < r by lia] using hsel
    · by_cases hir' : i + 1 = r
      · have hsel := D.selected_of_strictAt ht.1
        rw [hlast.symm, halias] at hsel
        have hi' : i = r - 1 := by lia
        simp only [w, show i < r by lia, ite_true, show ¬ (i + 1 < r) by lia, ite_false,
          show i + 1 - r = 0 by lia]
        rw [hi']
        exact hsel
      · have hj : i - r + 1 < r := by lia
        have hsel := D.selected_of_strictAt (hstrictQ (i - r + 1) hj)
        rw [hbQ (i - r) hj] at hsel
        simp only [w, show ¬ (i < r) by lia, show ¬ (i + 1 < r) by lia, ite_false,
          show i + 1 - r = i - r + 1 by lia]
        exact hsel
  have hdist := walk_step_distinct D ha r (by lia) w hstep
  refine ⟨⟨r, P, t, hr2, hb, hbQ, fun j h1 h2 => (hs j h1 h2).1, hstrictQ, hx, hb0,
    ht.1, hlast.symm, halias, ht.boundary_gap D, harea3, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro i j hi hj hij
    have := hdist i j (by lia) (by lia) (by simpa [w, hi, hj] using hij)
    exact this
  · intro i j hi hj hij
    have := hdist (i + r) (j + r) (by lia) (by lia) (by
      simpa [w, show ¬ (i + r < r) by lia, show ¬ (j + r < r) by lia] using hij)
    lia
  · intro i j hi hj hij
    have := hdist i (j + r) (by lia) (by lia) (by
      simpa [w, hi, show ¬ (j + r < r) by lia] using hij)
    lia

end Diagram

namespace AliasContacts

variable {n : ℕ} {D : Diagram n} (K : AliasContacts D)

/-- The lower boundary of the initial ND row. -/
def β : ℤ := D.boundary (K.P 0)

theorem period_t : ∃ k : ℤ, K.t = K.P 0 + 1 + n * k := D.residue_eq_exists_period K.res_t

theorem res_β : D.residue K.β = D.residue (K.P (K.r - 1)) := by
  obtain ⟨k, hk⟩ := K.period_t
  have : D.boundary K.t = K.β + n * k := by rw [hk, D.boundary_add_period, K.b0]; rfl
  rw [← K.bt, this, D.residue_add_period]

theorem res_β1 : D.residue (K.β + 1) = D.residue (K.P (K.r - 1) + 1) := by
  rw [D.residue_succ, D.residue_succ, K.res_β]

theorem β_add_two_le : K.β + 2 ≤ K.P 0 := by
  have h := K.area_t
  rw [K.res_t] at h
  have hb := K.b0
  unfold Diagram.boundary at hb
  unfold β Diagram.boundary
  have : (D.area.area (D.residue (K.P 0 + 1)) : ℤ) ≥ 3 := by exact_mod_cast h
  lia

theorem P_add_two_le (j : ℕ) (hj : j + 1 < K.r) : K.P j + 2 ≤ K.P (j + 1) := by
  have hb := K.bP j hj
  have hs := D.strictAt_boundary_lt_self (K.strictP (j + 1) (by lia) hj)
  rw [hb] at hs
  by_contra hc
  have heq : K.P (j + 1) = K.P j + 1 := by lia
  exact K.nePQ (j + 1) j hj (by lia) (by rw [heq])

theorem P_lt_P_succ (j : ℕ) (hj : j + 1 < K.r) : K.P j < K.P (j + 1) := by
  have := K.P_add_two_le j hj; lia

theorem window_lt (z : ℤ) : z - D.boundary z < n := by
  have := D.self_sub_period_lt_boundary z; lia

end AliasContacts

end VerticalStripLLT.Circular
