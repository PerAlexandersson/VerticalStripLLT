import VerticalStripLLT.Path
import Mathlib.Tactic.Linarith

/-! Ordered, disjoint edge sets for the ordinary path decoder. -/

namespace VerticalStripLLT

namespace Step

theorem normalFrom_lower_bound (x y u v : ℕ) :
    ∀ {w : List Step}, normalFrom x y u v w = true → x ≤ u := by
  intro w h
  induction w generalizing x y with
  | nil => simp [normalFrom] at h
  | cons a w ih =>
      cases a <;>
        simp only [normalFrom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at *
      · exact ih (x := x) (y := y + 1) h
      · rcases ‹_› with h | h
        · exact h.1.1.symm.le
        · exact le_trans (Nat.le_succ x) (ih (x := x + 1) (y := y + 1) h)
      · rcases ‹_› with h | h
        · exact h.1.1.symm.le
        · exact le_trans (Nat.le_succ x) (ih (x := x + 1) (y := y) h)

theorem strictFrom_lower_bound (x y u v : ℕ) :
    ∀ {w : List Step}, strictFrom x y u v w = true → x ≤ u := by
  intro w h
  induction w generalizing x y with
  | nil => simp [strictFrom] at h
  | cons a w ih =>
      cases a <;>
        simp only [strictFrom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at *
      · exact ih (x := x) (y := y + 1) h
      · rcases ‹_› with h | h
        · exact h.1.symm.le
        · exact le_trans (Nat.le_succ x) (ih (x := x + 1) (y := y + 1) h)
      · exact le_trans (Nat.le_succ x) (ih (x := x + 1) (y := y) h)

theorem normalFrom_lt (x y u v : ℕ) {w : List Step} :
    normalFrom x y u v w = true → u < v := by
  intro h
  induction w generalizing x y with
  | nil => simp [normalFrom] at h
  | cons a w ih =>
      cases a <;>
        simp only [normalFrom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at *
      · exact ih (x := x) (y := y + 1) h
      · rcases ‹_› with h | h
        · rw [h.1.1]
          exact h.1.2
        · exact ih (x := x + 1) (y := y + 1) h
      · rcases ‹_› with h | h
        · rw [h.1.1]
          exact h.1.2
        · exact ih (x := x + 1) (y := y) h

theorem strictFrom_lt_of_valid (n x y u v : ℕ) {w : List Step} :
    validFrom n x y w = true → strictFrom x y u v w = true → u < v := by
  intro hv hs
  induction w generalizing n x y u v with
  | nil => simp [strictFrom] at hs
  | cons a w ih =>
      cases a with
      | north =>
          simp only [validFrom, strictFrom] at hv hs
          exact ih (n := n) (x := x) (y := y + 1) (u := u) (v := v) hv hs
      | diagonal =>
          simp only [validFrom, strictFrom, Bool.or_eq_true, Bool.and_eq_true,
            beq_iff_eq, decide_eq_true_eq] at hv hs
          rcases hs with h | h
          · have hxy : x < y := by simpa using hv.1
            have hux : u = x := h.1
            have hvy : v = y := h.2
            simpa [hux, hvy] using hxy
          · exact ih (n := n) (x := x + 1) (y := y + 1)
              (u := u) (v := v) hv.2 h
      | east =>
          simp only [validFrom, strictFrom, Bool.and_eq_true, decide_eq_true_eq] at hv hs
          exact ih (n := n) (x := x + 1) (y := y) (u := u) (v := v) hv.2 hs

theorem normalFrom_strictFrom_disjoint (x y u v : ℕ) {w : List Step} :
    normalFrom x y u v w = true → strictFrom x y u v w = true → False := by
  intro hn hs
  induction w generalizing x y with
  | nil => simp [normalFrom] at hn
  | cons a w ih =>
      cases a with
      | north =>
          simp only [normalFrom, strictFrom] at hn hs
          exact ih (x := x) (y := y + 1) hn hs
      | diagonal =>
          simp only [normalFrom, strictFrom, Bool.or_eq_true, Bool.and_eq_true,
            beq_iff_eq, decide_eq_true_eq] at hn hs
          rcases hn with hn | hn
          · rcases hs with hs | hs
            · have huv : v < y := hn.2
              have hvy : v = y := hs.2
              lia
            · have hxu : u = x := by
                exact hn.1.1
              have hlow : x + 1 ≤ u := strictFrom_lower_bound (x + 1) (y + 1) u v hs
              lia
          · rcases hs with hs | hs
            · have hxu : u = x := by
                exact hs.1
              have hlow : x + 1 ≤ u := normalFrom_lower_bound (x + 1) (y + 1) u v hn
              lia
            · exact ih (x := x + 1) (y := y + 1) hn hs
      | east =>
          simp only [normalFrom, strictFrom, Bool.or_eq_true, Bool.and_eq_true,
            beq_iff_eq, decide_eq_true_eq] at hn hs
          rcases hn with hn | hn
          · have hxu : u = x := by
              exact hn.1.1
            have hlow : x + 1 ≤ u := strictFrom_lower_bound (x + 1) y u v hs
            lia
          · exact ih (x := x + 1) (y := y) hn hs

end Step

namespace SchroderPath

theorem normalEdges_lt {n : ℕ} (P : SchroderPath n)
    {e : Fin n × Fin n} (he : e ∈ P.normalEdges) : e.1.val < e.2.val := by
  have h : Step.normalFrom 0 0 e.1.val e.2.val P.steps = true := by
    simpa [normalEdges] using he
  exact Step.normalFrom_lt 0 0 e.1.val e.2.val h

theorem strictEdges_lt {n : ℕ} (P : SchroderPath n)
    {e : Fin n × Fin n} (he : e ∈ P.strictEdges) : e.1.val < e.2.val := by
  have h : Step.strictFrom 0 0 e.1.val e.2.val P.steps = true := by
    simpa [strictEdges] using he
  exact Step.strictFrom_lt_of_valid n 0 0 e.1.val e.2.val P.valid h

theorem normalEdges_disjoint_strictEdges {n : ℕ} (P : SchroderPath n) :
    Disjoint P.normalEdges P.strictEdges := by
  refine Finset.disjoint_left.2 ?_
  intro e hn hs
  have hn' : Step.normalFrom 0 0 e.1.val e.2.val P.steps = true := by
    simpa [normalEdges] using hn
  have hs' : Step.strictFrom 0 0 e.1.val e.2.val P.steps = true := by
    simpa [strictEdges] using hs
  exact Step.normalFrom_strictFrom_disjoint 0 0 e.1.val e.2.val hn' hs'

end SchroderPath
end VerticalStripLLT
