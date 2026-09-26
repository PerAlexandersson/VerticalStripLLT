import VerticalStripLLT.OrientationShift

namespace VerticalStripLLT

noncomputable def xQShift (m : ℕ) : XPoly m →+* XPoly m :=
  MvPolynomial.map qShift

theorem evalElementary_qShiftMap (m : ℕ) (f : EExpansion) :
    evalElementary m (qShiftMap f) =
      xQShift m (evalElementary m f) := by
  have heq : (evalElementary m).comp qShiftMap =
      (xQShift m).comp (evalElementary m) := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simp [evalElementary, qShiftMap, xQShift]
    · intro k
      simp only [RingHom.coe_comp, Function.comp_apply, qShiftMap,
        evalElementary, xQShift, MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
      rw [MvPolynomial.map_esymm]
  exact RingHom.congr_fun heq f

theorem xQShift_evalElementary_orientationExpansion {n m : ℕ}
    (P : SchroderPath n) :
    xQShift m (evalElementary m (orientationExpansion P)) =
      evalElementary m (shiftedOrientationExpansion P) := by
  rw [← qShift_orientationExpansion P]
  exact (evalElementary_qShiftMap m (orientationExpansion P)).symm

end VerticalStripLLT
