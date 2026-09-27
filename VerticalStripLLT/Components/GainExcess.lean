import VerticalStripLLT.Components.GainSlack
import VerticalStripLLT.Components.GainFeasibility
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A positive signed gain excess forces a strictly slack optional edge. -/

namespace VerticalStripLLT.Components.GainData

open scoped BigOperators
open Classical

noncomputable section

variable {V E : Type*} (G : GainData V E)

private theorem list_sum_map_sub {α : Type*} (l : List α) (f g : α → ℤ) :
    (l.map (fun a => f a - g a)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map, List.sum_cons, ih]
      ring

/- The endpoint potential sums agree after transporting the displayed
   permutation through `p`.  Keeping this as a separate lemma makes the
   cancellation of endpoint terms explicit. -/
theorem endpoint_potential_sum_eq {P N : List E} {p : V → ℕ}
    (hperm :
      (P.map G.head ++ N.map G.tail).Perm
        (P.map G.tail ++ N.map G.head)) :
    (P.map (fun e => (p (G.head e) : ℤ))).sum +
        (N.map (fun e => (p (G.tail e) : ℤ))).sum =
      (P.map (fun e => (p (G.tail e) : ℤ))).sum +
        (N.map (fun e => (p (G.head e) : ℤ))).sum := by
  have h := (hperm.map (fun v : V => (p v : ℤ))).sum_eq
  simpa [List.map_append, Function.comp_def] using h

theorem gain_sum_le_of_no_slack {A : Finset E} {P N : List E} {p : V → ℕ}
    (hP : ∀ e ∈ P, e ∈ A)
    (hfeas : G.Feasible A p)
    (hperm :
      (P.map G.head ++ N.map G.tail).Perm
        (P.map G.tail ++ N.map G.head))
    (hno : ∀ e ∈ N,
      ¬((p (G.tail e) : ℤ) + G.gain e < p (G.head e))) :
    (P.map G.gain).sum ≤ (N.map G.gain).sum := by
  have hPgain :
      (P.map G.gain).sum ≤
        (P.map (fun e =>
          (p (G.head e) : ℤ) - (p (G.tail e) : ℤ))).sum := by
    apply List.sum_le_sum
    intro e he
    have he' := hfeas e (hP e he)
    lia
  have hNgain :
      (N.map (fun e =>
        (p (G.head e) : ℤ) - (p (G.tail e) : ℤ))).sum ≤
        (N.map G.gain).sum := by
    apply List.sum_le_sum
    intro e he
    have he' := le_of_not_gt (hno e he)
    lia
  have hendpoint := G.endpoint_potential_sum_eq (p := p) hperm
  have hdiff :
      (P.map (fun e =>
        (p (G.head e) : ℤ) - (p (G.tail e) : ℤ))).sum =
        (N.map (fun e =>
          (p (G.head e) : ℤ) - (p (G.tail e) : ℤ))).sum := by
    rw [list_sum_map_sub, list_sum_map_sub]
    linarith
  exact hPgain.trans (hdiff.le.trans hNgain)

/-- A positive gain excess around a closed endpoint walk supplies a strict
slack edge among the optional edges.  The lists may contain repeated or
parallel edge instances. -/
theorem exists_slack_of_gain_excess {A : Finset E} {P N : List E} {p : V → ℕ}
    (hP : ∀ e ∈ P, e ∈ A)
    (hfeas : G.Feasible A p)
    (hperm :
      (P.map G.head ++ N.map G.tail).Perm
        (P.map G.tail ++ N.map G.head))
    (hexcess : (N.map G.gain).sum < (P.map G.gain).sum) :
    ∃ e ∈ N, (p (G.tail e) : ℤ) + G.gain e < p (G.head e) := by
  by_contra h
  have hno : ∀ e ∈ N,
      ¬((p (G.tail e) : ℤ) + G.gain e < p (G.head e)) := by
    intro e he hs
    exact h ⟨e, he, hs⟩
  have hle := G.gain_sum_le_of_no_slack hP hfeas hperm hno
  exact (not_lt_of_ge hle) hexcess

/-! A closed-walk excess can be passed directly to the powerset
involution from `GainSlack`. -/
theorem sum_powerset_feasible_eq_zero_of_gain_excess [DecidableEq E]
    (A N : Finset E) (P Nsteps : List E)
    (hN : ∀ e ∈ Nsteps, e ∈ N)
    (hP : ∀ e ∈ P, e ∈ A)
    (hperm :
      (P.map G.head ++ Nsteps.map G.tail).Perm
        (P.map G.tail ++ Nsteps.map G.head))
    (hexcess : (Nsteps.map G.gain).sum < (P.map G.gain).sum) :
    (∑ J ∈ N.powerset,
      if ∃ p, G.Feasible (A ∪ J) p then (-1 : ℤ) ^ J.card else 0) = 0 := by
  apply G.sum_powerset_feasible_eq_zero A N
  intro J _hJ hgood
  have hP' : ∀ e ∈ P, e ∈ A ∪ J := by
    intro e he
    exact Finset.mem_union_left J (hP e he)
  obtain ⟨e, he, hs⟩ := G.exists_slack_of_gain_excess hP'
    (G.potential_feasible hgood) hperm hexcess
  exact ⟨e, Finset.mem_filter.mpr ⟨hN e he, hs⟩⟩

/-- The closed-walk form of the finite excess cancellation, with no feasibility
or pivot premise left over. -/
theorem sum_powerset_closedWalksNonpos_eq_zero_of_gain_excess
    [Fintype V] [DecidableEq E]
    (A N : Finset E) (P Nsteps : List E)
    (hN : ∀ e ∈ Nsteps, e ∈ N)
    (hP : ∀ e ∈ P, e ∈ A)
    (hperm :
      (P.map G.head ++ Nsteps.map G.tail).Perm
        (P.map G.tail ++ Nsteps.map G.head))
    (hexcess : (Nsteps.map G.gain).sum < (P.map G.gain).sum) :
    (∑ J ∈ N.powerset,
      if G.ClosedWalksNonpos (A ∪ J) then (-1 : ℤ) ^ J.card else 0) = 0 := by
  simpa only [G.exists_feasible_iff_closedWalksNonpos] using
    G.sum_powerset_feasible_eq_zero_of_gain_excess A N P Nsteps hN hP hperm hexcess

end

end VerticalStripLLT.Components.GainData
