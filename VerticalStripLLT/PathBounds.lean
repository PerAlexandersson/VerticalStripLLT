import VerticalStripLLT.PathInvariants

/-! Endpoint bounds needed to separate the graph components of concatenated paths. -/

namespace VerticalStripLLT

namespace Step

theorem validFrom_bounds (n x y : ℕ) {w : List Step}
    (hv : validFrom n x y w = true) : x ≤ n ∧ y ≤ n := by
  induction w generalizing n x y with
  | nil =>
      simp only [validFrom, Bool.and_eq_true, beq_iff_eq] at hv
      exact ⟨by lia, by lia⟩
  | cons a w ih =>
      cases a with
      | north =>
          simp only [validFrom] at hv
          have h := ih (n := n) (x := x) (y := y + 1) hv
          exact ⟨h.1, by lia⟩
      | diagonal =>
          simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hv
          have h := ih (n := n) (x := x + 1) (y := y + 1) hv.2
          exact ⟨by lia, by lia⟩
      | east =>
          simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hv
          have h := ih (n := n) (x := x + 1) (y := y) hv.2
          exact ⟨by lia, h.2⟩

theorem normalFrom_upper_bound (n x y u v : ℕ) {w : List Step}
    (hv : validFrom n x y w = true)
    (he : normalFrom x y u v w = true) : v < n := by
  induction w generalizing x y u v with
  | nil => simp [normalFrom] at he
  | cons a w ih =>
      cases a with
      | north =>
          simp only [validFrom, normalFrom] at hv he
          exact ih (x := x) (y := y + 1) (u := u) (v := v) hv he
      | diagonal =>
          simp only [validFrom, normalFrom, Bool.or_eq_true, Bool.and_eq_true,
            beq_iff_eq, decide_eq_true_eq] at hv he
          rcases he with he | he
          · have h : y + 1 ≤ n := (validFrom_bounds n (x + 1) (y + 1) hv.2).2
            have hvy : v < y := he.2
            lia
          · exact ih (x := x + 1) (y := y + 1) (u := u) (v := v) hv.2 he
      | east =>
          simp only [validFrom, normalFrom, Bool.or_eq_true, Bool.and_eq_true,
            beq_iff_eq, decide_eq_true_eq] at hv he
          rcases he with he | he
          · have h : y ≤ n := (validFrom_bounds n (x + 1) y hv.2).2
            have hvy : v < y := he.2
            lia
          · exact ih (x := x + 1) (y := y) (u := u) (v := v) hv.2 he

theorem strictFrom_upper_bound (n x y u v : ℕ) {w : List Step}
    (hv : validFrom n x y w = true)
    (he : strictFrom x y u v w = true) : v < n := by
  induction w generalizing x y u v with
  | nil => simp [strictFrom] at he
  | cons a w ih =>
      cases a with
      | north =>
          simp only [validFrom, strictFrom] at hv he
          exact ih (x := x) (y := y + 1) (u := u) (v := v) hv he
      | diagonal =>
          simp only [validFrom, strictFrom, Bool.or_eq_true, Bool.and_eq_true,
            beq_iff_eq, decide_eq_true_eq] at hv he
          rcases he with he | he
          · have h : y + 1 ≤ n := (validFrom_bounds n (x + 1) (y + 1) hv.2).2
            have hvy : v = y := he.2
            lia
          · exact ih (x := x + 1) (y := y + 1) (u := u) (v := v) hv.2 he
      | east =>
          simp only [validFrom, strictFrom, Bool.and_eq_true, decide_eq_true_eq] at hv he
          exact ih (x := x + 1) (y := y) (u := u) (v := v) hv.2 he

end Step
end VerticalStripLLT
