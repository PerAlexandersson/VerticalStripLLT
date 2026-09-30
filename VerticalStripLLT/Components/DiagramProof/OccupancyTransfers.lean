import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith

/-! A finite equal-sum occupancy descent by unit transfers. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

def occupancyDeficit {I State : Type*} [Fintype I]
    (count : State → I → ℕ) (τ σ : State) : ℕ :=
  ∑ i, (count τ i - count σ i)

theorem reflTransGen_of_occupancy_descent
    {I State : Type*} [Fintype I] [DecidableEq I]
    (count : State → I → ℕ) (step : State → State → Prop) (τ : State)
    (hinj : Function.Injective count)
    (hmove : ∀ (σ : State),
      (∑ i, count σ i) = ∑ i, count τ i →
      (∃ i, count σ i ≠ count τ i) →
      ∃ e f σ', count τ e < count σ e ∧ count σ f < count τ f ∧
        Relation.ReflTransGen step σ σ' ∧
        (∀ i, count σ' i =
          if i = e then count σ i - 1
          else if i = f then count σ i + 1
          else count σ i))
    {σ : State} (hsum : (∑ i, count σ i) = ∑ i, count τ i) :
    Relation.ReflTransGen step σ τ := by
  have sum_two (g : I → ℕ) (e f : I) (hef : e ≠ f) :
      (∑ i, g i) = g e + g f +
        ∑ i ∈ (Finset.univ.erase e).erase f, g i := by
    rw [← Finset.add_sum_erase Finset.univ g (Finset.mem_univ e)]
    rw [← Finset.add_sum_erase (Finset.univ.erase e) g
      (Finset.mem_erase.mpr ⟨hef.symm, Finset.mem_univ _⟩)]
    ac_rfl
  have hsum_update : ∀ {σ σ' : State} {e f : I}, e ≠ f →
      0 < count σ e →
      (∀ i, count σ' i =
        if i = e then count σ i - 1
        else if i = f then count σ i + 1
        else count σ i) →
      (∑ i, count σ' i) = ∑ i, count σ i := by
    intro σ σ' e f hef hpos hup
    have hres : (∑ i ∈ (Finset.univ.erase e).erase f, count σ' i) =
        ∑ i ∈ (Finset.univ.erase e).erase f, count σ i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hif := (Finset.mem_erase.mp hi).1
      have hie := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      simp [hup, hie, hif]
    rw [sum_two (count σ') e f hef, sum_two (count σ) e f hef, hres]
    have he' : count σ' e = count σ e - 1 := by simp [hup]
    have hf' : count σ' f = count σ f + 1 := by simp [hup, hef.symm]
    rw [he', hf']
    lia
  have aux : ∀ m : ℕ, ∀ σ : State,
      occupancyDeficit count τ σ = m →
      (∑ i, count σ i) = ∑ i, count τ i →
      Relation.ReflTransGen step σ τ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro σ hmeasure hsumσ
      by_cases heq : ∀ i, count σ i = count τ i
      · have hcount : count σ = count τ := funext heq
        have hstate : σ = τ := hinj hcount
        subst σ
        exact Relation.ReflTransGen.refl
      · obtain ⟨e, f, σ', he, hf, hpath, hupdate⟩ :=
          hmove σ hsumσ (not_forall.mp heq)
        have hef : e ≠ f := by
          intro h
          subst f
          lia
        have hsum' : (∑ i, count σ' i) = ∑ i, count τ i := by
          have hpos : 0 < count σ e := by lia
          rw [hsum_update hef hpos hupdate]
          exact hsumσ
        have hdeficit : occupancyDeficit count τ σ' <
            occupancyDeficit count τ σ := by
          unfold occupancyDeficit
          let gnew : I → ℕ := fun i => count τ i - count σ' i
          let gold : I → ℕ := fun i => count τ i - count σ i
          rw [show (∑ i, gnew i) = gnew e + gnew f +
              ∑ i ∈ (Finset.univ.erase e).erase f, gnew i from
            sum_two gnew e f hef]
          rw [show (∑ i, gold i) = gold e + gold f +
              ∑ i ∈ (Finset.univ.erase e).erase f, gold i from
            sum_two gold e f hef]
          have hres : (∑ i ∈ (Finset.univ.erase e).erase f, gnew i) =
              ∑ i ∈ (Finset.univ.erase e).erase f, gold i := by
            apply Finset.sum_congr rfl
            intro i hi
            have hif : i ≠ f := (Finset.mem_erase.mp hi).1
            have hie : i ≠ e := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
            simp [gnew, gold, hupdate, hie, hif]
          have he0 : count τ e - (count σ e - 1) =
              count τ e - count σ e := by lia
          have hf0 : count τ f - (count σ f + 1) + 1 =
              count τ f - count σ f := by lia
          have he' : count σ' e = count σ e - 1 := by
            simp [hupdate]
          have hf' : count σ' f = count σ f + 1 := by
            simp [hupdate, hef.symm]
          rw [hres]
          dsimp only [gnew, gold]
          rw [he', hf']
          lia
        exact hpath.trans (ih (occupancyDeficit count τ σ') (hdeficit.trans_le hmeasure.le) σ'
          rfl hsum')
  exact aux (occupancyDeficit count τ σ) σ rfl hsum

end

end VerticalStripLLT.Circular.DiagramProof
