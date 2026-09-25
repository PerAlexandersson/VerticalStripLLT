import VerticalStripLLT.OrientationConcat
import VerticalStripLLT.OrientationUnicellular

namespace VerticalStripLLT

theorem orientationExpansion_concat {n k : ℕ} (P : SchroderPath n)
    (R : SchroderPath k) :
    orientationExpansion (P.concat R) =
      orientationExpansion P * orientationExpansion R := by
  simpa only [orientationExpansion] using orientationExpansionAt_concat P R
    (Polynomial.X - 1)

theorem shiftedOrientationExpansion_concat {n k : ℕ} (P : SchroderPath n)
    (R : SchroderPath k) :
    shiftedOrientationExpansion (P.concat R) =
      shiftedOrientationExpansion P * shiftedOrientationExpansion R := by
  simpa only [shiftedOrientationExpansion] using orientationExpansionAt_concat P R
    Polynomial.X

theorem orientationExpansion_unicellular {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) :
    orientationExpansion (SchroderPath.resolveNorthEast U V h) -
        orientationExpansion (SchroderPath.resolveEastNorth U V h) =
      (MvPolynomial.C Polynomial.X - 1) * orientationExpansion
        (⟨U ++ Step.diagonal :: V, h⟩ : SchroderPath n) := by
  have hC : (MvPolynomial.C (Polynomial.X - 1) : EExpansion) =
      MvPolynomial.C Polynomial.X - 1 := by
    rw [map_sub, map_one]
  exact (orientationExpansionAt_unicellular U V h (Polynomial.X - 1)).trans
    (congrArg (fun a : EExpansion => a * orientationExpansion
      (⟨U ++ Step.diagonal :: V, h⟩ : SchroderPath n)) hC)

theorem shiftedOrientationExpansion_unicellular {n : ℕ} (U V : List Step)
    (h : Step.validFrom n 0 0 (U ++ Step.diagonal :: V) = true) :
    shiftedOrientationExpansion (SchroderPath.resolveNorthEast U V h) -
        shiftedOrientationExpansion (SchroderPath.resolveEastNorth U V h) =
      MvPolynomial.C Polynomial.X * shiftedOrientationExpansion
        (⟨U ++ Step.diagonal :: V, h⟩ : SchroderPath n) := by
  simpa only [shiftedOrientationExpansion] using
    orientationExpansionAt_unicellular U V h Polynomial.X

end VerticalStripLLT
