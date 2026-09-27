import VerticalStripLLT.Components.WeightedToggleCancellation
import VerticalStripLLT.Circular.EdgeColoring
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Signed deletion for the actual finite strict-coloring enumerator. -/

namespace VerticalStripLLT.Components

open Classical
open scoped BigOperators

noncomputable section

variable {V E : Type*} [DecidableEq E]

/-- Balanced endpoints force an optional ascent when all positive steps are strict. -/
theorem exists_optional_ascent (tail head : E → V) (P N : List E)
    (hP : P ≠ []) (c : V → ℕ) (hc : ∀ e ∈ P, c (tail e) < c (head e))
    (hperm : (P.map head ++ N.map tail).Perm (P.map tail ++ N.map head)) :
    ∃ e ∈ N, c (tail e) < c (head e) := by
  by_contra h
  have hN : ∀ e ∈ N, c (head e) ≤ c (tail e) := by
    intro e he
    exact le_of_not_gt (fun hlt => h ⟨e, he, hlt⟩)
  have hlt := List.sum_lt_sum_of_ne_nil hP (fun e => c (tail e))
    (fun e => c (head e)) hc
  have hle := List.sum_le_sum hN
  have heq := (hperm.map c).sum_eq
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def] at heq
  lia

/-- Per-coloring cancellation, with its actual monomial or any other fixed weight. -/
theorem coloring_signed_selection_sum_eq_zero {M : Type*} [AddCommGroup M]
    (tail head : E → V) (B N : Finset E) (P Nsteps : List E)
    (hP : P ≠ []) (hPB : ∀ e ∈ P, e ∈ B) (hN : ∀ e ∈ Nsteps, e ∈ N)
    (hperm : (P.map head ++ Nsteps.map tail).Perm (P.map tail ++ Nsteps.map head))
    (c : V → ℕ) (weight : M) :
    (∑ J ∈ N.powerset, if ∀ e ∈ B ∪ J, c (tail e) < c (head e)
      then ((-1 : ℤ) ^ J.card) • weight else 0) = 0 := by
  by_cases hc : ∀ e ∈ B, c (tail e) < c (head e)
  · obtain ⟨e, heN, he⟩ := exists_optional_ascent tail head P Nsteps hP c
      (fun e he => hc e (hPB e he)) hperm
    let Good (J : Finset E) := ∀ f ∈ B ∪ J, c (tail f) < c (head f)
    have hgood : ∀ J ∈ N.powerset, Good J → Good (toggleSubset (fun _ => e) J) := by
      intro J _ hJ f hf
      have hsub : B ∪ toggleSubset (fun _ => e) J ⊆ insert e (B ∪ J) := by
        intro a ha
        by_cases heJ : e ∈ J <;> simp only [toggleSubset, heJ, reduceIte] at ha
        all_goals
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at ha ⊢
          tauto
      rcases Finset.mem_insert.mp (hsub hf) with rfl | hf
      · exact he
      · exact hJ f hf
    have hcancel := sum_powerset_good_toggle_weighted_eq_zero N Good
      (fun _ => e) (fun _ => weight) (fun _ _ _ => hN e heN)
      hgood (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    convert hcancel using 1
    apply Finset.sum_congr rfl
    intro J _
    dsimp only [Good]
    split_ifs <;> rfl
  · apply Finset.sum_eq_zero
    intro J _
    have hbad : ¬∀ e ∈ B ∪ J, c (tail e) < c (head e) := by
      intro h
      exact hc (fun e he => h e (Finset.mem_union_left J he))
    simp only [hbad, ite_false]

end

end VerticalStripLLT.Components

namespace VerticalStripLLT.Circular.EdgeData

open Classical
open scoped BigOperators

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- Deletion recurrence for the independently defined strict-coloring polynomial. -/
theorem sum_powerset_strictOrderEnumerator_eq_zero (G : EdgeData V E)
    (A N : Finset E) (P Nsteps : List E)
    (hP : P ≠ []) (hPB : ∀ e ∈ P, e ∈ G.strict ∪ A)
    (hN : ∀ e ∈ Nsteps, e ∈ N)
    (hperm : (P.map G.head ++ Nsteps.map G.tail).Perm
      (P.map G.tail ++ Nsteps.map G.head)) (m : ℕ) :
    (∑ J ∈ N.powerset, ((-1 : ℤ) ^ J.card) • G.strictOrderEnumerator (A ∪ J) m) = 0 := by
  simp only [strictOrderEnumerator, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro c _
  have h := Components.coloring_signed_selection_sum_eq_zero G.tail G.head
    (G.strict ∪ A) N P Nsteps hP hPB hN hperm (fun v => (c v).val) (monomial c)
  simpa only [Finset.union_assoc, ← Fin.lt_def] using h

end

end VerticalStripLLT.Circular.EdgeData
