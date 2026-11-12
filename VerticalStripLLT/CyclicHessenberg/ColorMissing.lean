import VerticalStripLLT.CyclicHessenberg.ColorEvaluation
import Mathlib.Data.List.Sort

/-! Small support and sorted-insertion facts used by the coloring recurrence. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V : Type*} [LinearOrder V]

/-- Inserting a strict maximum appends it to the increasing finite-set sort. -/
theorem sort_insert_max (S : Finset V) (r : V)
    (hr : ∀ a ∈ S, a < r) :
    (insert r S).sort = S.sort ++ [r] := by
  classical
  apply List.SortedLT.eq_of_mem_iff
    (Finset.sortedLT_sort (insert r S))
    (List.sortedLT_append.mpr ⟨Finset.sortedLT_sort S, by simp,
      by
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst b
        exact hr a (by simpa only [Finset.mem_sort] using ha)⟩)
  intro a
  simp [Finset.mem_sort]

/-- A missing support vertex forces every color-class evaluation to vanish. -/
theorem colorClassProduct_eval_missing {R : Type*} [CommRing R]
    (S T : Finset V) (r : V) (hrS : r ∈ S) (hrT : r ∉ T)
    {m : ℕ} (weight : Fin m → R) (f : List V → R)
    (hf : ∀ w, ¬ IsOrder S w → f w = 0) :
    wordEval f [] [] (colorClassProduct T.sort (List.ofFn weight)) = 0 := by
  classical
  have hposition := colorClassProduct_eq_positionProduct T weight
  generalize hL : colorPositions T m = L at hposition
  rw [hposition, wordEval_prod_one_add]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hx
  have hnot : ¬ IsOrder S (U.map fun p : Fin m × T => p.2.val) := by
    intro horder
    have hrword : r ∈ U.map fun p : Fin m × T => p.2.val :=
      (horder.mem_iff r).mpr hrS
    obtain ⟨p, hp, hpr⟩ := List.mem_map.mp hrword
    exact hrT (hpr ▸ p.2.property)
  rw [hf _ hnot, mul_zero]

end VerticalStripLLT.CyclicHessenberg
