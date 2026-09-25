import VerticalStripLLT.SecondBouncePath
import VerticalStripLLT.BounceScanners

namespace VerticalStripLLT
namespace Step

/-- Swapping `north, diagonal` to `diagonal, north` is valid when the swap point lies
strictly above the diagonal. -/
theorem validFrom_northDiagonal_swap (n x y : ℕ) {U V : List Step}
    (h : validFrom n x y (U ++ north :: diagonal :: V) = true)
    (hlt : (endpointFrom x y U).1 < (endpointFrom x y U).2) :
    validFrom n x y (U ++ diagonal :: north :: V) = true := by
  induction U generalizing x y with
  | nil =>
      simp only [List.nil_append, validFrom, Bool.and_eq_true, decide_eq_true_eq,
        endpointFrom] at h hlt ⊢
      exact ⟨hlt, h.2⟩
  | cons s U ih =>
      cases s with
      | north =>
          simp only [List.cons_append, validFrom, endpointFrom] at h hlt ⊢
          exact ih (x := x) (y := y + 1) h hlt
      | diagonal =>
          simp only [List.cons_append, validFrom, Bool.and_eq_true,
            decide_eq_true_eq, endpointFrom] at h hlt ⊢
          exact ⟨h.1, ih (x := x + 1) (y := y + 1) h.2 hlt⟩
      | east =>
          simp only [List.cons_append, validFrom, Bool.and_eq_true,
            decide_eq_true_eq, endpointFrom] at h hlt ⊢
          exact ⟨h.1, ih (x := x + 1) (y := y) h.2 hlt⟩

/-- Endpoint equalities for the step blocks used in the third bounce. -/
theorem endpointFrom_thirdBounce_blocks (U V : List Step) :
    endpointFrom 0 0 (U ++ diagonal :: north :: V) =
        endpointFrom 0 0 (U ++ north :: diagonal :: V) ∧
      endpointFrom 0 0 (U ++ north :: north :: east :: V) =
        endpointFrom 0 0 (U ++ north :: diagonal :: V) ∧
      endpointFrom 0 0 ((U ++ [east]) ++ north :: north :: V) =
        endpointFrom 0 0 (U ++ north :: diagonal :: V) ∧
      (endpointFrom 0 0 (U ++ [east])).2 = (endpointFrom 0 0 U).2 := by
  simp only [endpointFrom_append, endpointFrom, List.append_assoc, List.cons_append,
    List.nil_append, and_self]

/-- The source corner lies strictly above the diagonal: `a < i`. -/
theorem thirdBounce_corner_lt (U V : List Step)
    (hreturn : (endpointFrom 0 0 U).2 =
      (endpointFrom 0 0 (U ++ north :: diagonal :: V)).1) :
    (endpointFrom 0 0 U).1 < (endpointFrom 0 0 U).2 := by
  have hE : endpointFrom 0 0 (U ++ north :: diagonal :: V) =
      endpointFrom ((endpointFrom 0 0 U).1 + 1) ((endpointFrom 0 0 U).2 + 1 + 1) V := by
    rw [endpointFrom_append]
    rfl
  have hm := endpointFrom_mono ((endpointFrom 0 0 U).1 + 1)
    ((endpointFrom 0 0 U).2 + 1 + 1) V
  rw [← hE] at hm
  lia

end Step
