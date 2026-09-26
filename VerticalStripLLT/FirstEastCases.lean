import VerticalStripLLT.BounceCoordinates
import VerticalStripLLT.PathSplit
import VerticalStripLLT.PrefixScanners

namespace VerticalStripLLT

open Step

/-- The first east step either returns to the diagonal, follows a north step
above the diagonal, or has an east-free bounce seed as its prefix. -/
theorem firstEast_prefix_cases {n : ℕ} (Y W : List Step)
    (hv : validFrom n 0 0 (Y ++ east :: W) = true) (hY : east ∉ Y) :
    (endpointFrom 0 0 Y).2 = (endpointFrom 0 0 Y).1 + 1 ∨
      (∃ U, Y = U ++ [north] ∧ east ∉ U ∧
        (endpointFrom 0 0 U).1 < (endpointFrom 0 0 U).2) ∨ BounceSeed Y := by
  have hs := validFrom_suffix n 0 0 Y (east :: W) hv
  have hg : (endpointFrom 0 0 Y).1 < (endpointFrom 0 0 Y).2 := by
    simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hs
    exact hs.1
  by_cases heq : (endpointFrom 0 0 Y).2 = (endpointFrom 0 0 Y).1 + 1
  · exact Or.inl heq
  have hgap : (endpointFrom 0 0 Y).1 + 1 < (endpointFrom 0 0 Y).2 := by lia
  right
  rcases List.eq_nil_or_concat' Y with hnil | ⟨U, s, hU⟩
  · simp [hnil, endpointFrom] at hg
  · cases s with
    | east => simp [hU] at hY
    | north =>
        left
        refine ⟨U, hU, ?_, ?_⟩
        · simpa [hU] using hY
        · simp only [hU, endpointFrom_append, endpointFrom] at hgap
          lia
    | diagonal =>
        right
        refine ⟨hY, ⟨U, hU⟩, ?_⟩
        simpa only [endpointFrom_noEast 0 0 Y hY, zero_add] using hgap

end VerticalStripLLT
