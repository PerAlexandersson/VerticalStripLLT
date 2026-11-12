import VerticalStripLLT.CyclicHessenberg.Kernel
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Finite signed sums of words, evaluated in arbitrary exterior contexts.
No quotient or multiplicativity assumption on the evaluating functional is used. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V R : Type*} [CommRing R]

abbrev WordSum (R V : Type*) [CommRing R] := MonoidAlgebra R (FreeMonoid V)

/-- A literal word with coefficient one. -/
def wordTerm (l : List V) : WordSum R V := MonoidAlgebra.single (FreeMonoid.ofList l) 1

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
    exact hd (by simp) (by simp)
  | add Y Z hY hZ =>
    simpa only [mul_add, add_mul, add_zero] using hY.add hZ
  | smul c Y hY =>
    simpa only [mul_smul_comm, smul_mul_assoc, smul_zero] using hY.smul c

end VerticalStripLLT.CyclicHessenberg
