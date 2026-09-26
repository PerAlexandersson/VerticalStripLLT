import VerticalStripLLT.AlphabetStability
import VerticalStripLLT.Expansion

namespace VerticalStripLLT

/-- Set the last k variables to zero by successive last-variable specializations. -/
noncomputable def specializeTail (m : ℕ) : (k : ℕ) → XPoly (m + k) →+* XPoly m
  | 0 => RingHom.id _
  | k + 1 => (specializeTail m k).comp (specializeLast (m + k))

theorem specializeTail_evalElementary (m k : ℕ) (f : EExpansion) :
    specializeTail m k (evalElementary (m + k) f) = evalElementary m f := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change specializeTail m k (specializeLast (m + k)
        (evalElementary (m + k + 1) f)) = evalElementary m f
      exact (congrArg (specializeTail m k)
        (RingHom.congr_fun (specializeLast_evalElementary (m + k)) f)).trans ih

/-- The coloring-defined family is compatible with deleting its final alphabet variable. -/
theorem specializeLast_coloringLLT {n : ℕ} (P : SchroderPath n) (m : ℕ) :
    specializeLast m (coloringLLT P (m + 1)) = coloringLLT P m := by
  rw [coloringLLT_eq_eval_orientationExpansion, coloringLLT_eq_eval_orientationExpansion]
  exact RingHom.congr_fun (specializeLast_evalElementary m) (orientationExpansion P)

/-- Alphabet stability holds for every path and any number of extra variables. -/
theorem specializeTail_coloringLLT {n : ℕ} (P : SchroderPath n) (m k : ℕ) :
    specializeTail m k (coloringLLT P (m + k)) = coloringLLT P m := by
  rw [coloringLLT_eq_eval_orientationExpansion, coloringLLT_eq_eval_orientationExpansion]
  exact specializeTail_evalElementary m k (orientationExpansion P)

end VerticalStripLLT
