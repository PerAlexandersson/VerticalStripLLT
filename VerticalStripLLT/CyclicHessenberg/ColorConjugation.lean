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

theorem descendingClass_append (t : R) (l u : List V) :
    descendingClass t (l ++ u) = descendingClass t u * descendingClass t l := by
  induction l with
  | nil => simp [descendingClass]
  | cons a l ih => simp only [List.cons_append, descendingClass, ih, mul_assoc]

theorem inverseClass_append (t : R) (l u : List V) :
    inverseClass t (l ++ u) = inverseClass t l * inverseClass t u := by
  induction l with
  | nil => simp [inverseClass]
  | cons a l ih => simp only [List.cons_append, inverseClass, ih, mul_assoc]

theorem wordLetterSum_append (l u : List V) :
    wordLetterSum (R := R) (l ++ u) = wordLetterSum l + wordLetterSum u := by
  induction l with
  | nil => simp [wordLetterSum]
  | cons a l ih => simp only [List.cons_append, wordLetterSum, ih, add_assoc]

/-- The class sum commutes with the sum of its individual letters in every context. -/
theorem letterSum_commute_descendingClass [LinearOrder V] (f : List V → R)
    (hf : ContextualBalance f) (hrep : ∀ l, ¬ l.Nodup → f l = 0)
    (t : R) (l : List V) (hl : l.Pairwise (· < ·)) :
    ContextEq f (wordLetterSum l * descendingClass t l)
      (descendingClass t l * wordLetterSum l) := by
  induction l using List.reverseRecOn with
  | nil => simp only [wordLetterSum, descendingClass, mul_one, one_mul]; exact ContextEq.refl _
  | append_singleton l v ih =>
    have hp := List.pairwise_append.mp hl
    let A : WordSum R V := wordLetterSum l
    let D : WordSum R V := descendingClass t l
    let u : WordSum R V := wordTerm [v]
    have hDA : ContextEq f (D * A) (A * D) := (ih hp.1).symm
    have hconj := descendingClass_conjugate_root f hf hrep t l v hp.1
      (fun a ha => hp.2.2 a ha v (by simp))
    have hID := inverseClass_mul_descendingClass f hrep t l
    have hDv : ContextEq f (D * u) ((u + t • wordComm A u) * D) := by
      have h₁ := (hID.mul_left (D * u)).symm
      have h₂ := hconj.mul_right D
      exact (by simpa only [mul_one, ← mul_assoc] using h₁).trans h₂
    have hR := (hDA.add hDv).mul_left (1 + t • u)
    have hzero : ContextEq f ((t * t) • ((u * A * u - u * u * A) * D)) 0 := by
      have h₁ : ContextEq f (u * A * u) 0 := repeated_sandwich f hrep v A
      have h₂ : ContextEq f (u * u * A) 0 := by
        simpa only [mul_one, zero_mul] using (repeated_sandwich f hrep v 1).mul_right A
      simpa only [sub_zero, zero_mul, smul_zero] using ((h₁.sub h₂).mul_right D).smul (t * t)
    have heq : (1 + t • u) * (A * D + (u + t • wordComm A u) * D) =
        (A + u) * ((1 + t • u) * D) +
          (t * t) • ((u * A * u - u * u * A) * D) := by
      simp only [wordComm, mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one,
        mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, smul_smul, mul_assoc]
      abel
    have hh := hR.trans ((ContextEq.of_eq heq).trans ((ContextEq.refl _).add hzero))
    simpa only [wordLetterSum_append, descendingClass_append, wordLetterSum,
      descendingClass, add_zero, one_mul, mul_add, add_zero, A, D, u] using hh.symm

/-- Inverse commutation follows from both inverse identities and the proved class commutation. -/
theorem letterSum_commute_inverseClass [LinearOrder V] (f : List V → R)
    (hf : ContextualBalance f) (hrep : ∀ l, ¬ l.Nodup → f l = 0)
    (t : R) (l : List V) (hl : l.Pairwise (· < ·)) :
    ContextEq f (wordLetterSum l * inverseClass t l)
      (inverseClass t l * wordLetterSum l) := by
  let A : WordSum R V := wordLetterSum l
  let D : WordSum R V := descendingClass t l
  let I : WordSum R V := inverseClass t l
  have hID := inverseClass_mul_descendingClass f hrep t l
  have hDI := descendingClass_mul_inverseClass f hrep t l
  have hDA := (letterSum_commute_descendingClass f hf hrep t l hl).symm
  have h₁ := ((hID.mul_right A).mul_right I).symm
  have h₂ := (hDA.mul_left I).mul_right I
  have h₃ := hDI.mul_left (I * A)
  have hh : ContextEq f (A * I) (I * A) := by
    apply (by simpa only [one_mul, mul_assoc] using h₁).trans
    apply (by simpa only [mul_assoc] using h₂).trans
    simpa only [mul_one, mul_assoc] using h₃
  exact hh

end VerticalStripLLT.CyclicHessenberg
