import VerticalStripLLT.MarkedDiagonal

/-! Valid local step swaps used to construct the single-bounce successor paths. -/

namespace VerticalStripLLT

namespace Step

theorem validFrom_diagonalNorth_swap (n x y : ℕ) {U V : List Step}
    (h : validFrom n x y (U ++ diagonal :: north :: V) = true) :
    validFrom n x y (U ++ north :: diagonal :: V) = true := by
  induction U generalizing x y with
  | nil =>
      simp only [List.nil_append, validFrom, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨by lia, h.2⟩
  | cons s U ih =>
      cases s with
      | north =>
          simp only [List.cons_append, validFrom] at h ⊢
          exact ih (x := x) (y := y + 1) h
      | diagonal =>
          simp only [List.cons_append, validFrom, Bool.and_eq_true,
            decide_eq_true_eq] at h ⊢
          exact ⟨h.1, ih (x := x + 1) (y := y + 1) h.2⟩
      | east =>
          simp only [List.cons_append, validFrom, Bool.and_eq_true,
            decide_eq_true_eq] at h ⊢
          exact ⟨h.1, ih (x := x + 1) (y := y) h.2⟩

theorem validFrom_diagonalEast_swap (n x y : ℕ) {U V : List Step}
    (h : validFrom n x y (U ++ diagonal :: east :: V) = true)
    (hgap : (endpointFrom x y U).1 + 1 < (endpointFrom x y U).2) :
    validFrom n x y (U ++ east :: diagonal :: V) = true := by
  induction U generalizing x y with
  | nil =>
      simp only [List.nil_append, validFrom, Bool.and_eq_true,
        decide_eq_true_eq] at h ⊢
      have hg : x + 1 < y := by simpa only [endpointFrom] using hgap
      exact ⟨h.1, ⟨hg, h.2.2⟩⟩
  | cons s U ih =>
      cases s with
      | north =>
          simp only [List.cons_append, validFrom] at h ⊢
          have hg : (endpointFrom x (y + 1) U).1 + 1 <
              (endpointFrom x (y + 1) U).2 := by
            simpa [endpointFrom] using hgap
          exact ih (x := x) (y := y + 1) h hg
      | diagonal =>
          simp only [List.cons_append, validFrom, Bool.and_eq_true,
            decide_eq_true_eq] at h ⊢
          have hg : (endpointFrom (x + 1) (y + 1) U).1 + 1 <
              (endpointFrom (x + 1) (y + 1) U).2 := by
            simpa [endpointFrom] using hgap
          exact ⟨h.1, ih (x := x + 1) (y := y + 1) h.2 hg⟩
      | east =>
          simp only [List.cons_append, validFrom, Bool.and_eq_true,
            decide_eq_true_eq] at h ⊢
          have hg : (endpointFrom (x + 1) y U).1 + 1 <
              (endpointFrom (x + 1) y U).2 := by
            simpa [endpointFrom] using hgap
          exact ⟨h.1, ih (x := x + 1) (y := y) h.2 hg⟩

end Step

namespace SchroderPath

def swapDiagonalNorth {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: Step.north :: V) = true) :
    SchroderPath n :=
  ⟨U ++ Step.north :: Step.diagonal :: V,
    Step.validFrom_diagonalNorth_swap n 0 0 h⟩

def swapDiagonalEast {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: Step.east :: V) = true)
    (hgap : (Step.endpointFrom 0 0 U).1 + 1 < (Step.endpointFrom 0 0 U).2) :
    SchroderPath n :=
  ⟨U ++ Step.east :: Step.diagonal :: V,
    Step.validFrom_diagonalEast_swap n 0 0 h hgap⟩

@[simp] theorem swapDiagonalNorth_steps {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: Step.north :: V) = true) :
    (swapDiagonalNorth U V h).steps = U ++ Step.north :: Step.diagonal :: V := rfl

@[simp] theorem swapDiagonalEast_steps {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: Step.east :: V) = true)
    (hgap : (Step.endpointFrom 0 0 U).1 + 1 < (Step.endpointFrom 0 0 U).2) :
    (swapDiagonalEast U V h hgap).steps = U ++ Step.east :: Step.diagonal :: V := rfl

end SchroderPath
end VerticalStripLLT
