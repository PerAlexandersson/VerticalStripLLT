import VerticalStripLLT.CyclicHessenberg.ColorClassSums

/-! Contextual conjugation of the largest vertex by finite color-class products. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V R : Type*} [CommRing R]

noncomputable def wordLetterSum : List V → WordSum R V
  | [] => 0
  | a :: l => wordTerm [a] + wordLetterSum l

noncomputable def wordComm (A B : WordSum R V) : WordSum R V := A * B - B * A

theorem ContextEq.comm {f : List V → R} {A B C D : WordSum R V}
    (h : ContextEq f A B) (h' : ContextEq f C D) :
    ContextEq f (wordComm A C) (wordComm B D) := (h.mul h').sub (h'.mul h)

theorem contextual_triple [LinearOrder V] {f : List V → R}
    (hf : ContextualBalance f) {a b c : V} (hab : a < b) (hbc : b < c) :
    ContextEq f (wordTerm [b] * wordComm (wordTerm [a]) (wordTerm [c]))
      (wordComm (wordTerm [a]) (wordTerm [c]) * wordTerm [b]) := by
  intro ρ σ
  simp only [wordComm, mul_sub, sub_mul, wordTerm_mul, map_sub, wordEval_term]
  simp only [List.cons_append, List.nil_append]
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [add_comm] using (hf ρ σ a b c hab hbc).symm

/-- If each letter commutes contextually with a sum, so does the full class product. -/
theorem descendingClass_commute (f : List V → R) (t : R) (l : List V)
    (Y : WordSum R V)
    (hY : ∀ a ∈ l, ContextEq f (wordTerm [a] * Y) (Y * wordTerm [a])) :
    ContextEq f (descendingClass t l * Y) (Y * descendingClass t l) := by
  induction l with
  | nil => simp only [descendingClass, one_mul, mul_one]; exact ContextEq.refl Y
  | cons a l ih =>
    have ha := hY a (by simp)
    have hl := ih (fun b hb => hY b (by simp [hb]))
    have hfactor : ContextEq f ((1 + t • wordTerm [a]) * Y)
        (Y * (1 + t • wordTerm [a])) := by
      simpa only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
        mul_smul_comm] using (ContextEq.refl Y).add (ha.smul t)
    have h₁ := hfactor.mul_left (descendingClass t l)
    have h₂ := hl.mul_right (1 + t • wordTerm [a])
    exact (ContextEq.of_eq (mul_assoc _ _ _)).trans
      (h₁.trans ((ContextEq.of_eq (mul_assoc _ _ _).symm).trans
        (h₂.trans (ContextEq.of_eq (mul_assoc _ _ _)))))

/-- Conjugation fixes a sum commuting with every smaller vertex. -/
theorem descendingClass_conj_of_commute (f : List V → R)
    (hrep : ∀ l, ¬ l.Nodup → f l = 0) (t : R) (l : List V) (Y : WordSum R V)
    (hY : ∀ a ∈ l, ContextEq f (wordTerm [a] * Y) (Y * wordTerm [a])) :
    ContextEq f (descendingClass t l * Y * inverseClass t l) Y := by
  have hc := (descendingClass_commute f t l Y hY).mul_right (inverseClass t l)
  have hi := (descendingClass_mul_inverseClass f hrep t l).mul_left Y
  exact hc.trans ((ContextEq.of_eq (mul_assoc _ _ _)).trans (by
    simpa only [mul_one] using hi))

/-- The cubic relation removes every term of degree at least two in this conjugation. -/
theorem descendingClass_conjugate_root [LinearOrder V] (f : List V → R)
    (hf : ContextualBalance f) (hrep : ∀ l, ¬ l.Nodup → f l = 0)
    (t : R) (l : List V) (r : V) (hl : l.Pairwise (· < ·))
    (hr : ∀ a ∈ l, a < r) :
    ContextEq f (descendingClass t l * wordTerm [r] * inverseClass t l)
      (wordTerm [r] + t • wordComm (wordLetterSum l) (wordTerm [r])) := by
  induction l with
  | nil =>
    simp only [descendingClass, inverseClass, wordLetterSum, wordComm, zero_mul,
      mul_zero, sub_zero, smul_zero, add_zero, one_mul, mul_one]
    exact ContextEq.refl _
  | cons a l ih =>
    have hpair := List.pairwise_cons.mp hl
    have hsmall : ∀ b ∈ l, b < r := fun b hb => hr b (by simp [hb])
    have htail := ih hpair.2 hsmall
    let C : WordSum R V := wordComm (wordTerm [a]) (wordTerm [r])
    have hfix : ContextEq f (descendingClass t l * C * inverseClass t l) C :=
      descendingClass_conj_of_commute f hrep t l C
        (fun b hb => contextual_triple hf (hpair.1 b hb) (hsmall b hb))
    have h₁ := ((letter_conjugation f hrep t a (wordTerm [r])).mul_left
      (descendingClass t l)).mul_right (inverseClass t l)
    have h₁' : ContextEq f
        (descendingClass t (a :: l) * wordTerm [r] * inverseClass t (a :: l))
        (descendingClass t l * wordTerm [r] * inverseClass t l +
          t • (descendingClass t l * C * inverseClass t l)) := by
      simpa only [descendingClass, inverseClass, mul_assoc, mul_add, add_mul,
        mul_smul_comm, smul_mul_assoc, wordComm, C] using h₁
    have h₂ := htail.add (hfix.smul t)
    apply h₁'.trans
    apply h₂.trans
    apply ContextEq.of_eq
    simp only [wordLetterSum, wordComm, add_mul, mul_add, smul_sub, smul_add, C]
    abel

end VerticalStripLLT.CyclicHessenberg
