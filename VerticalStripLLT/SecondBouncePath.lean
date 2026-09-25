import VerticalStripLLT.BouncePath
import VerticalStripLLT.PrefixScanners

/-! Construct the second-bounce successor by composing two valid local swaps. -/

namespace VerticalStripLLT

namespace Step

theorem endpointFrom_diagonalNorth_swap (x y : ℕ) (U V : List Step) :
    endpointFrom x y (U ++ diagonal :: north :: V) =
      endpointFrom x y (U ++ north :: diagonal :: V) := by
  rw [endpointFrom_append, endpointFrom_append]
  simp [endpointFrom]

end Step

namespace SchroderPath

def secondBounceSuccessor {n : ℕ} (U V W : List Step)
    (h : Step.validFrom n 0 0
      ((U ++ Step.diagonal :: Step.north :: V) ++
        Step.diagonal :: Step.east :: W) = true)
    (hgap : (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).1 + 1 <
      (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).2) :
    SchroderPath n := by
  have h₁ : Step.validFrom n 0 0
      (U ++ Step.diagonal :: (Step.north :: V ++ Step.diagonal :: Step.east :: W)) = true := by
    simpa [List.append_assoc] using h
  have h₂ := Step.validFrom_diagonalNorth_swap n 0 0 h₁
  have h₂' : Step.validFrom n 0 0
      ((U ++ Step.north :: Step.diagonal :: V) ++ Step.diagonal :: Step.east :: W) = true := by
    simpa [List.append_assoc] using h₂
  have hgap' :
      (Step.endpointFrom 0 0 (U ++ Step.north :: Step.diagonal :: V)).1 + 1 <
        (Step.endpointFrom 0 0 (U ++ Step.north :: Step.diagonal :: V)).2 := by
    rw [← Step.endpointFrom_diagonalNorth_swap 0 0 U V]
    exact hgap
  exact ⟨(U ++ Step.north :: Step.diagonal :: V) ++
      Step.east :: Step.diagonal :: W,
    Step.validFrom_diagonalEast_swap n 0 0 h₂' hgap'⟩

@[simp] theorem secondBounceSuccessor_steps {n : ℕ} (U V W : List Step)
    (h : Step.validFrom n 0 0
      ((U ++ Step.diagonal :: Step.north :: V) ++
        Step.diagonal :: Step.east :: W) = true)
    (hgap : (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).1 + 1 <
      (Step.endpointFrom 0 0 (U ++ Step.diagonal :: Step.north :: V)).2) :
    (secondBounceSuccessor U V W h hgap).steps =
      (U ++ Step.north :: Step.diagonal :: V) ++ Step.east :: Step.diagonal :: W := rfl

end SchroderPath
end VerticalStripLLT
