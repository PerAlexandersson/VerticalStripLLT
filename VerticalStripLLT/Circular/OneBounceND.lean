import VerticalStripLLT.Circular.OneBounceNDGeometry
import VerticalStripLLT.Circular.FirstBounceRecurrences
import VerticalStripLLT.Circular.SecondBounceRecurrences

/-! Assembly of the four corner relations, two NN relations and one DN relation for both
actual shifted models, and the resulting one-bounce ND identity. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT

theorem qShift_injective : Function.Injective qShift := by
  have key : ∀ r : Q, (qShift r).comp (Polynomial.X - 1) = r := by
    intro r
    simp [qShift, Polynomial.comp_assoc]
  intro p q h
  rw [← key p, ← key q, h]

theorem xQShift_injective (m : ℕ) : Function.Injective (xQShift m) :=
  MvPolynomial.map_injective _ qShift_injective

theorem xQShift_C (m : ℕ) (p : Q) :
    xQShift m (MvPolynomial.C p : XPoly m) = MvPolynomial.C (qShift p) := by
  rw [xQShift, MvPolynomial.map_C]

theorem qShift_X : qShift Polynomial.X = Polynomial.X + 1 := by
  simp [qShift]

theorem qShift_X_sub_one : qShift (Polynomial.X - 1) = Polynomial.X := by
  simp [qShift]

end VerticalStripLLT

namespace VerticalStripLLT.Circular.Diagram

/-- Substituting the seven local relations and cancelling `q`. -/
theorem nd_cancel {R : Type*} [CommRing R] [IsDomain R]
    {X cD cN cE cS cJ cNs cJs cQ cEs cR : R} (hX : X ≠ 0)
    (e1 : cN = X * cD + cE) (e2 : cE = X * cS + cJ) (e3 : cN = (X + 1) * cNs)
    (e4 : cJ = (X + 1) * cJs) (e5 : cS = cQ) (e6 : cNs = X * cQ + cEs)
    (e7 : cEs = X * cR + cJs) : cD = X * cQ + (X + 1) * cR := by
  apply mul_left_cancel₀ hX
  linear_combination -e1 + e3 - e2 + (X + 1) * e6 - e4 + (X + 1) * e7 - X * e5

namespace NDLocalData

open scoped Classical

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.NDLocalData t)

section Coloring

variable (m : ℕ)

theorem col_e1 : xQShift m (B.ndN.coloringLLT m) =
    MvPolynomial.C Polynomial.X * xQShift m (D.coloringLLT m) +
      xQShift m (B.ndE.coloringLLT m) :=
  D.xQShift_coloringLLT_unstrict_corner B.g B.hg m

theorem col_e2 : xQShift m (B.ndE.coloringLLT m) =
    MvPolynomial.C Polynomial.X * xQShift m (B.lowered.coloringLLT m) +
      xQShift m (B.ndJ.coloringLLT m) :=
  B.ndE.xQShift_coloringLLT_corner B.ell B.ell_corner B.ell_not_mem_ndE m

theorem col_e3 : xQShift m (B.ndN.coloringLLT m) =
    MvPolynomial.C (Polynomial.X + 1) * xQShift m (B.ndNs.coloringLLT m) :=
  B.ndN.xQShift_coloringLLT_shortenStrict_NN B.fN B.fN_mem B.rootLength B.gapN B.ndN_hsame
    B.ndN_hleft B.ndN_hright m

theorem col_e4 : xQShift m (B.ndJ.coloringLLT m) =
    MvPolynomial.C (Polynomial.X + 1) * xQShift m (B.ndJs.coloringLLT m) :=
  B.ndJ.xQShift_coloringLLT_shortenStrict_NN B.fJ B.fJ_mem B.rootLength B.gapJ B.ndJ_hsame
    B.ndJ_hleft B.ndJ_hright m

theorem col_e5 : xQShift m (B.lowered.coloringLLT m) = xQShift m (B.shortened.coloringLLT m) := by
  rw [← B.dnS_eq]
  exact B.lowered.xQShift_coloringLLT_dnSuccessor B.ellS B.fS B.ellS_mem B.fS_mem B.fS_ne_ellS
    B.fS_contact B.lowered_heq B.lowered_hb B.lowered_hns B.rootLength B.gapS m

theorem col_e6 : xQShift m (B.ndNs.coloringLLT m) =
    MvPolynomial.C Polynomial.X * xQShift m (B.shortened.coloringLLT m) +
      xQShift m (B.ndEs.coloringLLT m) := by
  rw [ndNs_eq]
  exact B.shortened.xQShift_coloringLLT_unstrict_corner B.gQ B.gQ_mem m

theorem col_e7 : xQShift m (B.ndEs.coloringLLT m) =
    MvPolynomial.C Polynomial.X * xQShift m (B.ndR.coloringLLT m) +
      xQShift m (B.ndJs.coloringLLT m) := by
  rw [← ndEs_strictify_eq, ← ndEs_deleteCorner_eq]
  exact B.ndEs.xQShift_coloringLLT_corner B.ellEs B.ellEs_corner B.ellEs_not_mem m

/-- The shifted coloring form of the ND identity. -/
theorem xQShift_coloringLLT_nd : xQShift m (D.coloringLLT m) =
    MvPolynomial.C Polynomial.X * xQShift m (B.shortened.coloringLLT m) +
      MvPolynomial.C (Polynomial.X + 1) * xQShift m (B.ndR.coloringLLT m) := by
  have hX : (MvPolynomial.C Polynomial.X : XPoly m) ≠ 0 :=
    (MvPolynomial.C_eq_zero).not.mpr Polynomial.X_ne_zero
  have h1 : (MvPolynomial.C (Polynomial.X + 1) : XPoly m) = MvPolynomial.C Polynomial.X + 1 := by
    rw [map_add, map_one]
  have e3 := B.col_e3 m
  have e4 := B.col_e4 m
  rw [h1] at e3 e4 ⊢
  exact nd_cancel hX (B.col_e1 m) (B.col_e2 m) e3 e4 (B.col_e5 m) (B.col_e6 m) (B.col_e7 m)

/-- The unshifted coloring form of the ND identity. -/
theorem coloringLLT_nd : D.coloringLLT m =
    MvPolynomial.C (Polynomial.X - 1) * B.shortened.coloringLLT m +
      MvPolynomial.C Polynomial.X * B.ndR.coloringLLT m := by
  apply xQShift_injective m
  rw [B.xQShift_coloringLLT_nd m, (xQShift m).map_add, (xQShift m).map_mul,
    (xQShift m).map_mul, xQShift_C, xQShift_C, qShift_X, qShift_X_sub_one]

end Coloring

section Expansion

theorem exp_e1 : shiftedOrientationExpansion B.ndN =
    MvPolynomial.C Polynomial.X * shiftedOrientationExpansion D +
      shiftedOrientationExpansion B.ndE :=
  D.shiftedOrientationExpansion_unstrict_corner B.g B.hg

theorem exp_e2 : shiftedOrientationExpansion B.ndE =
    MvPolynomial.C Polynomial.X * shiftedOrientationExpansion B.lowered +
      shiftedOrientationExpansion B.ndJ :=
  B.ndE.shiftedOrientationExpansion_corner B.ell B.ell_corner B.ell_not_mem_ndE

theorem exp_e3 : shiftedOrientationExpansion B.ndN =
    MvPolynomial.C (Polynomial.X + 1) * shiftedOrientationExpansion B.ndNs :=
  B.ndN.shiftedOrientationExpansion_shortenStrict_NN B.fN B.fN_mem B.rootLength B.gapN
    B.ndN_hsame B.ndN_hleft B.ndN_hright

theorem exp_e4 : shiftedOrientationExpansion B.ndJ =
    MvPolynomial.C (Polynomial.X + 1) * shiftedOrientationExpansion B.ndJs :=
  B.ndJ.shiftedOrientationExpansion_shortenStrict_NN B.fJ B.fJ_mem B.rootLength B.gapJ
    B.ndJ_hsame B.ndJ_hleft B.ndJ_hright

theorem exp_e5 : shiftedOrientationExpansion B.lowered =
    shiftedOrientationExpansion B.shortened := by
  rw [← B.dnS_eq]
  exact B.lowered.shiftedOrientationExpansion_dnSuccessor B.ellS B.fS B.ellS_mem B.fS_mem
    B.fS_ne_ellS B.fS_contact B.lowered_heq B.lowered_hb B.lowered_hns B.rootLength B.gapS

theorem exp_e6 : shiftedOrientationExpansion B.ndNs =
    MvPolynomial.C Polynomial.X * shiftedOrientationExpansion B.shortened +
      shiftedOrientationExpansion B.ndEs := by
  rw [ndNs_eq]
  exact B.shortened.shiftedOrientationExpansion_unstrict_corner B.gQ B.gQ_mem

theorem exp_e7 : shiftedOrientationExpansion B.ndEs =
    MvPolynomial.C Polynomial.X * shiftedOrientationExpansion B.ndR +
      shiftedOrientationExpansion B.ndJs := by
  rw [← ndEs_strictify_eq, ← ndEs_deleteCorner_eq]
  exact B.ndEs.shiftedOrientationExpansion_corner B.ellEs B.ellEs_corner B.ellEs_not_mem

/-- The shifted HRV expansion form of the ND identity. -/
theorem shiftedOrientationExpansion_nd : shiftedOrientationExpansion D =
    MvPolynomial.C Polynomial.X * shiftedOrientationExpansion B.shortened +
      MvPolynomial.C (Polynomial.X + 1) * shiftedOrientationExpansion B.ndR := by
  have hX : (MvPolynomial.C Polynomial.X : EExpansion) ≠ 0 :=
    (MvPolynomial.C_eq_zero).not.mpr Polynomial.X_ne_zero
  have h1 : (MvPolynomial.C (Polynomial.X + 1) : EExpansion) =
      MvPolynomial.C Polynomial.X + 1 := by
    rw [map_add, map_one]
  have e3 := B.exp_e3
  have e4 := B.exp_e4
  rw [h1] at e3 e4 ⊢
  exact nd_cancel hX B.exp_e1 B.exp_e2 e3 e4 B.exp_e5 B.exp_e6 B.exp_e7

end Expansion

end NDLocalData
end VerticalStripLLT.Circular.Diagram

namespace VerticalStripLLT.Circular.Diagram

/-- The full actual ND identity for one bounce point on a circular diagram. -/
theorem exists_oneBounce_nd_reduction {n : ℕ} (D : Diagram n) {t x : ℤ}
    (ht : D.EligibleDE t) (h : ReverseBounceN D t x 0)
    (hx : ¬ D.strictAt x) (hx1 : D.strictAt (x + 1)) :
    ∃ Q R : Diagram n,
      Q.doubledArea + 2 = D.doubledArea ∧
      R.doubledArea + 4 = D.doubledArea ∧
      (∀ m : ℕ, D.coloringLLT m =
        MvPolynomial.C (Polynomial.X - 1) * Q.coloringLLT m +
          MvPolynomial.C Polynomial.X * R.coloringLLT m) ∧
      shiftedOrientationExpansion D =
        MvPolynomial.C Polynomial.X * shiftedOrientationExpansion Q +
          MvPolynomial.C (Polynomial.X + 1) * shiftedOrientationExpansion R := by
  obtain ⟨B⟩ := D.exists_ndLocalData ht h hx hx1
  exact ⟨B.shortened, B.ndR, B.shortened_doubledArea, B.ndR_doubledArea, B.coloringLLT_nd,
    B.shiftedOrientationExpansion_nd⟩

end VerticalStripLLT.Circular.Diagram
