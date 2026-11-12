import VerticalStripLLT.CyclicHessenberg.ColorClassSums
import Mathlib.Data.List.Sublists

/-! Literal expansions of the finite color-class products over sublists. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V R : Type*} [CommRing R]

private theorem sum_flatMap_pair {α M : Type*} [AddCommMonoid M] (l : List α)
    (f g : α → M) :
    (l.flatMap fun x => [f x, g x]).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc, add_left_comm]

private theorem sum_map_sublists_cons {M : Type*} [AddCommMonoid M] (a : V)
    (l : List V) (f : List V → M) :
    ((List.sublists (a :: l)).map f).sum =
      ((List.sublists l).map f).sum +
        ((List.sublists l).map fun s => f (a :: s)).sum := by
  rw [List.sublists_cons, List.bind_eq_flatMap, List.map_flatMap]
  exact sum_flatMap_pair _ _ _

private theorem sum_mul_right {M : Type*} [Semiring M] (l : List M) (y : M) :
    l.sum * y = (l.map fun x => x * y).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, add_mul]

private theorem mul_sum_left {M : Type*} [Semiring M] (y : M) (l : List M) :
    y * l.sum = (l.map fun x => y * x).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, mul_add]

private theorem sum_map_eq {α M : Type*} [AddCommMonoid M] (l : List α)
    (f g : α → M) (h : ∀ x ∈ l, f x = g x) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

private theorem sum_map_neg {α M : Type*} [AddCommGroup M] (l : List α) (f : α → M) :
    (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, add_comm]

/-- Expand the decreasing color-class product as a sum over sublists. -/
theorem descendingClass_eq_sublistSum (t : R) (l : List V) :
    descendingClass t l =
      (l.sublists.map fun s => t ^ s.length • wordTerm (R := R) s.reverse).sum := by
  induction l with
  | nil => simp [descendingClass, List.sublists_nil, wordTerm_nil]
  | cons a l ih =>
    rw [descendingClass, ih]
    rw [sum_map_sublists_cons]
    have hprod :
        ((l.sublists.map fun s => t ^ s.length • wordTerm (R := R) s.reverse).sum) *
            (1 + t • wordTerm (R := R) [a]) =
          (l.sublists.map fun s => t ^ s.length • wordTerm (R := R) s.reverse).sum +
            (l.sublists.map fun s =>
              (t ^ s.length • wordTerm (R := R) s.reverse) *
                (t • wordTerm (R := R) [a])).sum := by
      rw [mul_add, mul_one, sum_mul_right]
      simp only [List.map_map, Function.comp_def]
    rw [hprod]
    congr 1
    apply sum_map_eq
    intro s hs
    simp [List.length_cons, List.reverse_cons, wordTerm_mul, pow_succ,
      smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

/-- Expand the signed increasing color-class product as a sum over sublists. -/
theorem inverseClass_eq_sublistSum (t : R) (l : List V) :
    inverseClass t l =
      (l.sublists.map fun s => (-t) ^ s.length • wordTerm (R := R) s).sum := by
  induction l with
  | nil => simp [inverseClass, List.sublists_nil, wordTerm_nil]
  | cons a l ih =>
    rw [inverseClass, ih]
    rw [sum_map_sublists_cons]
    have hprod :
        (1 - t • wordTerm (R := R) [a]) *
            (l.sublists.map fun s => (-t) ^ s.length • wordTerm (R := R) s).sum =
          (l.sublists.map fun s => (-t) ^ s.length • wordTerm (R := R) s).sum -
            (l.sublists.map fun s =>
              (t • wordTerm (R := R) [a]) *
                ((-t) ^ s.length • wordTerm (R := R) s)).sum := by
      rw [sub_mul, one_mul, mul_sum_left]
      simp only [List.map_map, Function.comp_def]
    rw [hprod]
    have hterm (s : List V) :
        -((t • wordTerm (R := R) [a]) *
          ((-t) ^ s.length • wordTerm (R := R) s)) =
          (-t) ^ (a :: s).length • wordTerm (R := R) (a :: s) := by
      simp [List.length_cons, wordTerm_mul, pow_succ, smul_mul_assoc,
        mul_smul_comm, smul_smul, mul_comm]
    rw [sub_eq_add_neg, ← sum_map_neg]
    congr 1
    apply sum_map_eq
    intro s hs
    exact hterm s

end VerticalStripLLT.CyclicHessenberg
