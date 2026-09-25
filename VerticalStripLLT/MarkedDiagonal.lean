import VerticalStripLLT.UnicellularPath
import VerticalStripLLT.PathBounds

/-! The vertex pair determined by a marked diagonal in a valid path word. -/

namespace VerticalStripLLT

namespace Step

def endpointFrom (x y : ℕ) : List Step → ℕ × ℕ
  | [] => (x, y)
  | north :: w => endpointFrom x (y + 1) w
  | diagonal :: w => endpointFrom (x + 1) (y + 1) w
  | east :: w => endpointFrom (x + 1) y w

theorem validFrom_suffix (n x y : ℕ) (U V : List Step)
    (h : validFrom n x y (U ++ V) = true) :
    validFrom n (endpointFrom x y U).1 (endpointFrom x y U).2 V = true := by
  induction U generalizing x y with
  | nil => simpa [endpointFrom] using h
  | cons s U ih =>
      cases s with
      | north =>
          simp only [List.cons_append, endpointFrom, validFrom] at h ⊢
          exact ih (x := x) (y := y + 1) h
      | diagonal =>
          simp only [List.cons_append, endpointFrom, validFrom, Bool.and_eq_true,
            decide_eq_true_eq] at h ⊢
          exact ih (x := x + 1) (y := y + 1) h.2
      | east =>
          simp only [List.cons_append, endpointFrom, validFrom, Bool.and_eq_true,
            decide_eq_true_eq] at h ⊢
          exact ih (x := x + 1) (y := y) h.2

theorem strictFrom_marked (x y : ℕ) (U V : List Step) :
    strictFrom x y (endpointFrom x y U).1 (endpointFrom x y U).2
      (U ++ diagonal :: V) = true := by
  induction U generalizing x y with
  | nil => simp [endpointFrom, strictFrom]
  | cons s U ih =>
      cases s with
      | north =>
          simpa [List.cons_append, endpointFrom, strictFrom] using
            ih (x := x) (y := y + 1)
      | diagonal =>
          have h := ih (x := x + 1) (y := y + 1)
          simp [List.cons_append, endpointFrom, strictFrom, h]
      | east =>
          have h := ih (x := x + 1) (y := y)
          simp [List.cons_append, endpointFrom, strictFrom, h]

theorem markedDiagonal_bounds (n x y : ℕ) (U V : List Step)
    (h : validFrom n x y (U ++ diagonal :: V) = true) :
    (endpointFrom x y U).1 < (endpointFrom x y U).2 ∧
      (endpointFrom x y U).2 < n := by
  have hs := validFrom_suffix n x y U (diagonal :: V) h
  simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hs
  have ht := validFrom_bounds n
    ((endpointFrom x y U).1 + 1) ((endpointFrom x y U).2 + 1) hs.2
  exact ⟨hs.1, by lia⟩

end Step

namespace SchroderPath

def markedDiagonalEdge {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) : Fin n × Fin n := by
  classical
  have hb := Step.markedDiagonal_bounds n 0 0 U V h
  exact
    (⟨(Step.endpointFrom 0 0 U).1, hb.1.trans hb.2⟩,
      ⟨(Step.endpointFrom 0 0 U).2, hb.2⟩)

theorem markedDiagonalEdge_mem {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) :
    markedDiagonalEdge U V h ∈
      (⟨U ++ Step.diagonal :: V, h⟩ : SchroderPath n).strictEdges := by
  classical
  simp only [strictEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  change Step.strictFrom 0 0 (Step.endpointFrom 0 0 U).1
    (Step.endpointFrom 0 0 U).2 (U ++ Step.diagonal :: V) = true
  exact Step.strictFrom_marked 0 0 U V

end SchroderPath
end VerticalStripLLT
