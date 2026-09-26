import VerticalStripLLT.Circular.Diagram
import Mathlib.Tactic.Linarith

/-! The three-cell decrease at an overlapping ND contact. -/

namespace VerticalStripLLT.Circular.CircularArea

open scoped Classical

variable {n : ℕ} (A : CircularArea n)

noncomputable def aliasLowerValues (i j : Fin n) : Fin n → ℕ :=
  Function.update (Function.update A.area j (A.area j - 2)) i (A.area i - 1)

theorem aliasLowerValues_le (i j v : Fin n) : A.aliasLowerValues i j v ≤ A.area v := by
  unfold aliasLowerValues
  by_cases hv : v = i
  · subst v; rw [Function.update_self]; lia
  · rw [Function.update_of_ne hv]
    by_cases hj : v = j
    · subst v; rw [Function.update_self]; lia
    · rw [Function.update_of_ne hj]

theorem aliasLowerValues_left (i j : Fin n) :
    A.aliasLowerValues i j i = A.area i - 1 := Function.update_self _ _ _

theorem aliasLowerValues_right (i j : Fin n) (hne : j ≠ i) :
    A.aliasLowerValues i j j = A.area j - 2 := by
  unfold aliasLowerValues
  rw [Function.update_of_ne hne, Function.update_self]

theorem aliasLowerValues_other (i j v : Fin n) (hi : v ≠ i) (hj : v ≠ j) :
    A.aliasLowerValues i j v = A.area v := by
  unfold aliasLowerValues
  rw [Function.update_of_ne hi, Function.update_of_ne hj]

/-- Lower the predecessor row by one and the strict root row by two. -/
noncomputable def aliasLower (i j : Fin n) (hnext : A.next i = j)
    (harea : A.area j = A.area i + 1) (hlen : 3 ≤ A.area j)
    (hgap : A.area (A.next j) < A.area j) : CircularArea n where
  positive := A.positive
  area := A.aliasLowerValues i j
  bound v := (A.aliasLowerValues_le i j v).trans_lt (A.bound v)
  cyclic := by
    intro v
    have hne : j ≠ i := by intro h; rw [h] at harea; lia
    change A.aliasLowerValues i j (A.next v) ≤ A.aliasLowerValues i j v + 1
    by_cases hv : v = i
    · subst v
      rw [hnext, A.aliasLowerValues_right i j hne, A.aliasLowerValues_left]
      lia
    by_cases hvj : v = j
    · subst v
      rw [A.aliasLowerValues_right i j hne]
      by_cases hni : A.next j = i
      · rw [hni, A.aliasLowerValues_left]
        lia
      · have hnj : A.next j ≠ j := by intro h; rw [h] at hgap; lia
        rw [A.aliasLowerValues_other i j _ hni hnj]
        lia
    · rw [A.aliasLowerValues_other i j _ hv hvj]
      exact (A.aliasLowerValues_le i j _).trans (A.cyclic v)

end VerticalStripLLT.Circular.CircularArea
