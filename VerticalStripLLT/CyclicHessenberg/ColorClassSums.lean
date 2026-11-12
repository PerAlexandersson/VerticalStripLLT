import VerticalStripLLT.CyclicHessenberg.Kernel
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.NoncommRing

/-! Finite signed sums of words, evaluated in arbitrary exterior contexts.
No quotient or multiplicativity assumption on the evaluating functional is used. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V R : Type*} [CommRing R]

abbrev WordSum (R V : Type*) [CommRing R] := MonoidAlgebra R (FreeMonoid V)

/-- A literal word with coefficient one. -/
noncomputable def wordTerm (l : List V) : WordSum R V :=
  MonoidAlgebra.single (FreeMonoid.ofList l) 1

@[simp] theorem wordTerm_mul (l t : List V) :
    wordTerm (R := R) l * wordTerm t = wordTerm (l ++ t) := by
  simp [wordTerm, MonoidAlgebra.single_mul_single, FreeMonoid.ofList_append]

@[simp] theorem wordTerm_nil : wordTerm (R := R) ([] : List V) = 1 := rfl

/-- Evaluation is linear, and deliberately is not declared multiplicative. -/
noncomputable def wordEval (f : List V → R) (ρ σ : List V) : WordSum R V →ₗ[R] R :=
  (Finsupp.linearCombination R (fun w : FreeMonoid V => f (ρ ++ w.toList ++ σ))).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] theorem wordEval_term (f : List V → R) (ρ σ l : List V) :
    wordEval f ρ σ (wordTerm l) = f (ρ ++ l ++ σ) := by
  simp [wordEval, wordTerm, Finsupp.linearCombination_single]

private theorem wordEval_of (f : List V → R) (ρ σ : List V) (w : FreeMonoid V) :
    wordEval f ρ σ (MonoidAlgebra.of R (FreeMonoid V) w) =
      f (ρ ++ w.toList ++ σ) := by
  exact wordEval_term f ρ σ w.toList

theorem wordEval_term_mul (f : List V → R) (ρ σ l : List V) (A : WordSum R V) :
    wordEval f ρ σ (wordTerm l * A) = wordEval f (ρ ++ l) σ A := by
  induction A using MonoidAlgebra.induction_on with
  | of w =>
    change wordEval f ρ σ (wordTerm l * wordTerm w.toList) = _
    simp only [wordTerm_mul, wordEval_term, wordEval_of, List.append_assoc]
  | add A B hA hB => simp only [mul_add, map_add, hA, hB]
  | smul c A hA => simp only [mul_smul_comm, map_smul, hA]

theorem wordEval_mul_term (f : List V → R) (ρ σ l : List V) (A : WordSum R V) :
    wordEval f ρ σ (A * wordTerm l) = wordEval f ρ (l ++ σ) A := by
  induction A using MonoidAlgebra.induction_on with
  | of w =>
    change wordEval f ρ σ (wordTerm w.toList * wordTerm l) = _
    simp only [wordTerm_mul, wordEval_term, wordEval_of, List.append_assoc]
  | add A B hA hB => simp only [add_mul, map_add, hA, hB]
  | smul c A hA => simp only [smul_mul_assoc, map_smul, hA]

/-- Equality under every fixed row of letters on either side. -/
def ContextEq (f : List V → R) (A B : WordSum R V) : Prop :=
  ∀ ρ σ, wordEval f ρ σ A = wordEval f ρ σ B

namespace ContextEq

variable {f : List V → R} {A B C D : WordSum R V}

@[refl] theorem refl (A : WordSum R V) : ContextEq f A A := fun _ _ => rfl

@[symm] theorem symm (h : ContextEq f A B) : ContextEq f B A := fun ρ σ => (h ρ σ).symm

@[trans] theorem trans (h : ContextEq f A B) (h' : ContextEq f B C) :
    ContextEq f A C := fun ρ σ => (h ρ σ).trans (h' ρ σ)

theorem add (h : ContextEq f A B) (h' : ContextEq f C D) :
    ContextEq f (A + C) (B + D) := by
  intro ρ σ
  simp only [map_add, h ρ σ, h' ρ σ]

theorem sub (h : ContextEq f A B) (h' : ContextEq f C D) :
    ContextEq f (A - C) (B - D) := by
  intro ρ σ
  simp only [map_sub, h ρ σ, h' ρ σ]

theorem smul (h : ContextEq f A B) (c : R) : ContextEq f (c • A) (c • B) := by
  intro ρ σ
  simp only [map_smul, h ρ σ]

/-- Fixed contexts extend to arbitrary finite linear combinations of contexts. -/
theorem mul_left (h : ContextEq f A B) (C : WordSum R V) :
    ContextEq f (C * A) (C * B) := by
  induction C using MonoidAlgebra.induction_on with
  | of w =>
    intro ρ σ
    change wordEval f ρ σ (wordTerm w.toList * A) =
      wordEval f ρ σ (wordTerm w.toList * B)
    simpa only [wordEval_term_mul] using h (ρ ++ w.toList) σ
  | add C D hC hD => simpa only [add_mul] using hC.add hD
  | smul c C hC => simpa only [smul_mul_assoc] using hC.smul c

theorem mul_right (h : ContextEq f A B) (C : WordSum R V) :
    ContextEq f (A * C) (B * C) := by
  induction C using MonoidAlgebra.induction_on with
  | of w =>
    intro ρ σ
    change wordEval f ρ σ (A * wordTerm w.toList) =
      wordEval f ρ σ (B * wordTerm w.toList)
    simpa only [wordEval_mul_term] using h ρ (w.toList ++ σ)
  | add C D hC hD => simpa only [mul_add] using hC.add hD
  | smul c C hC => simpa only [mul_smul_comm] using hC.smul c

theorem mul (h : ContextEq f A B) (h' : ContextEq f C D) :
    ContextEq f (A * C) (B * D) :=
  (h.mul_right C).trans (h'.mul_left B)

theorem of_eq (h : A = B) : ContextEq f A B := h ▸ refl A

theorem sum {ι : Type*} (s : Finset ι) (A B : ι → WordSum R V)
    (h : ∀ i ∈ s, ContextEq f (A i) (B i)) :
    ContextEq f (∑ i ∈ s, A i) (∑ i ∈ s, B i) := by
  intro ρ σ
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun i hi => h i hi ρ σ)

end ContextEq

/-- Arbitrary finite sum contexts give exactly the same notion of equality. -/
theorem contextEq_iff_all_contexts (f : List V → R) (A B : WordSum R V) :
    ContextEq f A B ↔ ∀ L K : WordSum R V,
      wordEval f [] [] (L * A * K) = wordEval f [] [] (L * B * K) := by
  constructor
  · intro h L K
    exact ((h.mul_left L).mul_right K) [] []
  · intro h ρ σ
    simpa only [wordEval_mul_term, wordEval_term_mul, List.nil_append,
      List.append_nil] using h (wordTerm ρ) (wordTerm σ)

/-- The given contextual four-term relation holds in the finite word sums. -/
theorem ContextualBalance.word_relation [LinearOrder V] {f : List V → R}
    (hf : ContextualBalance f) {a b c : V} (hab : a < b) (hbc : b < c) :
    ContextEq f (wordTerm [a, c, b] + wordTerm [b, c, a])
      (wordTerm [c, a, b] + wordTerm [b, a, c]) := by
  intro ρ σ
  simpa only [map_add, wordEval_term] using hf ρ σ a b c hab hbc

/-- Repeated vertices vanish in every exterior context of a full-support functional. -/
theorem repeated_sandwich (f : List V → R)
    (hf : ∀ l, ¬ l.Nodup → f l = 0) (a : V) (Y : WordSum R V) :
    ContextEq f (wordTerm [a] * Y * wordTerm [a]) 0 := by
  induction Y using MonoidAlgebra.induction_on with
  | of w =>
    intro ρ σ
    change wordEval f ρ σ (wordTerm [a] * wordTerm w.toList * wordTerm [a]) = _
    rw [wordTerm_mul, wordTerm_mul, wordEval_term, map_zero]
    apply hf
    intro hnd
    have hnd' : ((ρ ++ [a]) ++ (w.toList ++ [a] ++ σ)).Nodup := by
      simpa only [List.append_assoc] using hnd
    have hd := (List.nodup_append'.mp hnd').2.2
    exact hd (show a ∈ ρ ++ [a] by simp) (by simp)
  | add Y Z hY hZ =>
    simpa only [mul_add, add_mul, add_zero] using hY.add hZ
  | smul c Y hY =>
    simpa only [mul_smul_comm, smul_mul_assoc, smul_zero] using hY.smul c

/-- Decreasing color-class product on a list supplied in increasing order. -/
noncomputable def descendingClass (t : R) : List V → WordSum R V
  | [] => 1
  | a :: l => descendingClass t l * (1 + t • wordTerm [a])

/-- Its signed increasing product; inverse identities are contextual. -/
noncomputable def inverseClass (t : R) : List V → WordSum R V
  | [] => 1
  | a :: l => (1 - t • wordTerm [a]) * inverseClass t l

theorem letter_inverse (f : List V → R) (hf : ∀ l, ¬ l.Nodup → f l = 0)
    (t : R) (a : V) :
    ContextEq f ((1 + t • wordTerm [a]) * (1 - t • wordTerm [a])) 1 := by
  have hsq : ContextEq f ((t • wordTerm [a]) * (t • wordTerm [a])) 0 := by
    have hh := (repeated_sandwich f hf a 1).smul (t * t)
    simpa only [mul_one, smul_zero, smul_mul_assoc, mul_smul_comm, smul_smul] using hh
  have heq : (1 + t • wordTerm [a]) * (1 - t • wordTerm [a]) =
      (1 : WordSum R V) - (t • wordTerm [a]) * (t • wordTerm [a]) := by
    generalize t • wordTerm (R := R) [a] = X
    noncomm_ring
  exact (ContextEq.of_eq heq).trans (by simpa using (ContextEq.refl 1).sub hsq)

theorem inverse_letter (f : List V → R) (hf : ∀ l, ¬ l.Nodup → f l = 0)
    (t : R) (a : V) :
    ContextEq f ((1 - t • wordTerm [a]) * (1 + t • wordTerm [a])) 1 := by
  simpa only [neg_smul, sub_eq_add_neg, neg_neg] using letter_inverse f hf (-t) a

/-- Both finite color-class products cancel in every exterior context. -/
theorem descendingClass_mul_inverseClass (f : List V → R)
    (hf : ∀ l, ¬ l.Nodup → f l = 0) (t : R) (l : List V) :
    ContextEq f (descendingClass t l * inverseClass t l) 1 := by
  induction l with
  | nil => simp only [descendingClass, inverseClass, mul_one]; exact ContextEq.refl 1
  | cons a l ih =>
    have hh := ((letter_inverse f hf t a).mul_left (descendingClass t l)).mul_right
      (inverseClass t l)
    have hs : ContextEq f (descendingClass t (a :: l) * inverseClass t (a :: l))
        (descendingClass t l * inverseClass t l) := by
      simpa only [descendingClass, inverseClass, mul_assoc, mul_one, one_mul] using hh
    exact hs.trans ih

theorem inverseClass_mul_descendingClass (f : List V → R)
    (hf : ∀ l, ¬ l.Nodup → f l = 0) (t : R) (l : List V) :
    ContextEq f (inverseClass t l * descendingClass t l) 1 := by
  induction l with
  | nil => simp only [descendingClass, inverseClass, mul_one]; exact ContextEq.refl 1
  | cons a l ih =>
    have hh := (ih.mul_left (1 - t • wordTerm [a])).mul_right (1 + t • wordTerm [a])
    have hs : ContextEq f (inverseClass t (a :: l) * descendingClass t (a :: l))
        ((1 - t • wordTerm [a]) * (1 + t • wordTerm [a])) := by
      simpa only [descendingClass, inverseClass, mul_assoc, mul_one] using hh
    exact hs.trans (inverse_letter f hf t a)

/-- The discarded quadratic term repeats the letter on both sides of an arbitrary sum. -/
theorem letter_conjugation (f : List V → R) (hf : ∀ l, ¬ l.Nodup → f l = 0)
    (t : R) (a : V) (Y : WordSum R V) :
    ContextEq f ((1 + t • wordTerm [a]) * Y * (1 - t • wordTerm [a]))
      (Y + t • (wordTerm [a] * Y - Y * wordTerm [a])) := by
  have hh := (repeated_sandwich f hf a Y).smul (t * t)
  have heq : (1 + t • wordTerm [a]) * Y * (1 - t • wordTerm [a]) =
      (Y + t • (wordTerm [a] * Y - Y * wordTerm [a])) -
        (t * t) • (wordTerm [a] * Y * wordTerm [a]) := by
    simp only [add_mul, mul_sub, one_mul, mul_one,
      smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
    abel
  exact (ContextEq.of_eq heq).trans (by
    simpa only [smul_zero, sub_zero] using (ContextEq.refl _).sub hh)

end VerticalStripLLT.CyclicHessenberg
