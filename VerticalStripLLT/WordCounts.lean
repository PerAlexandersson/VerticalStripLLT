import VerticalStripLLT.MarkedDiagonal

namespace VerticalStripLLT

namespace Step

def eastCount (w : List Step) : ℕ := w.count east

def northCount (w : List Step) : ℕ := w.count north

def diagonalCount (w : List Step) : ℕ := w.count diagonal

theorem endpointFrom_counts (x y : ℕ) (w : List Step) :
    endpointFrom x y w =
      (x + eastCount w + diagonalCount w,
        y + northCount w + diagonalCount w) := by
  induction w generalizing x y with
  | nil => simp [endpointFrom, eastCount, northCount, diagonalCount]
  | cons s w ih =>
    cases s <;>
      simp only [endpointFrom] <;>
      rw [ih] <;>
      simp [eastCount, northCount, diagonalCount, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

theorem validFrom_endpoint (n x y : ℕ) (w : List Step)
    (hv : validFrom n x y w = true) : endpointFrom x y w = (n, n) := by
  have hs := validFrom_suffix n x y w [] (by simpa only [List.append_nil] using hv)
  simp only [validFrom, Bool.and_eq_true, beq_iff_eq] at hs
  exact Prod.ext hs.1 hs.2

end Step

namespace SchroderPath

theorem northCount_eq_eastCount {n : ℕ} (P : SchroderPath n) :
    Step.northCount P.steps = Step.eastCount P.steps := by
  have h := Step.validFrom_endpoint n 0 0 P.steps P.valid
  rw [Step.endpointFrom_counts] at h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  lia

end SchroderPath
end VerticalStripLLT
