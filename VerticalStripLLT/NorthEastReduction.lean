import VerticalStripLLT.UnicellularPath
import VerticalStripLLT.FirstEast
import VerticalStripLLT.PrefixScanners

namespace VerticalStripLLT

namespace Step

theorem validFrom_contractNorthEast (n x y : ℕ) {U V : List Step}
    (h : validFrom n x y (U ++ north :: east :: V) = true)
    (hgap : (endpointFrom x y U).1 < (endpointFrom x y U).2) :
    validFrom n x y (U ++ diagonal :: V) = true := by
  induction U generalizing x y with
  | nil =>
      simp only [List.nil_append, validFrom, Bool.and_eq_true,
        decide_eq_true_eq] at h ⊢
      exact ⟨hgap, h.2⟩
  | cons s U ih =>
      cases s with
      | north =>
          simp only [List.cons_append, validFrom] at h ⊢
          exact ih (x := x) (y := y + 1) h hgap
      | diagonal =>
          simp only [List.cons_append, validFrom, Bool.and_eq_true,
            decide_eq_true_eq] at h ⊢
          exact ⟨h.1, ih (x := x + 1) (y := y + 1) h.2 hgap⟩
      | east =>
          simp only [List.cons_append, validFrom, Bool.and_eq_true,
            decide_eq_true_eq] at h ⊢
          exact ⟨h.1, ih (x := x + 1) (y := y) h.2 hgap⟩

theorem validFrom_swapNorthEast (n x y : ℕ) {U V : List Step}
    (h : validFrom n x y (U ++ north :: east :: V) = true)
    (hgap : (endpointFrom x y U).1 < (endpointFrom x y U).2) :
    validFrom n x y (U ++ east :: north :: V) = true := by
  exact (validFrom_resolve n x y (validFrom_contractNorthEast n x y h hgap)).2

theorem eastCount_northEast_contract (U V : List Step) :
    eastCount (U ++ north :: east :: V) =
      eastCount (U ++ diagonal :: V) + 1 := by
  simp [eastCount, Nat.add_assoc]

theorem eastCount_northEast_swap (U V : List Step) :
    eastCount (U ++ north :: east :: V) = eastCount (U ++ east :: north :: V) := by
  simp [eastCount]

theorem firstEastHeight_northEast_swap (U V : List Step) (hU : east ∉ U) :
    firstEastHeight (U ++ north :: east :: V) =
      firstEastHeight (U ++ east :: north :: V) + 1 := by
  have hs := firstEastHeight_append_east (U ++ [north]) V (by simpa using hU)
  have ht := firstEastHeight_append_east U (north :: V) hU
  simp only [List.append_assoc, List.singleton_append] at hs ht ⊢
  rw [hs, ht]
  simp [endpointFrom_append, endpointFrom]

end Step

namespace SchroderPath

def contractNorthEast {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.north :: Step.east :: V) = true)
    (hgap : (Step.endpointFrom 0 0 U).1 < (Step.endpointFrom 0 0 U).2) :
    SchroderPath n :=
  ⟨U ++ Step.diagonal :: V, Step.validFrom_contractNorthEast n 0 0 h hgap⟩

def swapNorthEast {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.north :: Step.east :: V) = true)
    (hgap : (Step.endpointFrom 0 0 U).1 < (Step.endpointFrom 0 0 U).2) :
    SchroderPath n :=
  ⟨U ++ Step.east :: Step.north :: V, Step.validFrom_swapNorthEast n 0 0 h hgap⟩

@[simp] theorem contractNorthEast_steps {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.north :: Step.east :: V) = true)
    (hgap : (Step.endpointFrom 0 0 U).1 < (Step.endpointFrom 0 0 U).2) :
    (contractNorthEast U V h hgap).steps = U ++ Step.diagonal :: V := rfl

@[simp] theorem swapNorthEast_steps {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.north :: Step.east :: V) = true)
    (hgap : (Step.endpointFrom 0 0 U).1 < (Step.endpointFrom 0 0 U).2) :
    (swapNorthEast U V h hgap).steps = U ++ Step.east :: Step.north :: V := rfl

end SchroderPath
end VerticalStripLLT
