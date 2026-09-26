import VerticalStripLLT.Circular.NDSeparatedCycles
set_option backward.isDefEq.respectTransparency false


/-! The seven actual relations (four corner relations, full NN twice and full DN once, the
latter vanishing on both sides when `S` is cyclic) for both shifted models, and the resulting
separated ND identity. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ}

namespace NDSeparatedHyp

variable {D : Diagram n} {t x : ℤ} {k : ℕ} (H : NDSeparatedHyp D t x k)

/-- Full DN for `S`, or simultaneous vanishing when `S` (hence `Q`) is cyclic. -/
theorem dS_dQ_models :
    (∀ m : ℕ, xQShift m (H.dS.coloringLLT m) = xQShift m (H.dQ.coloringLLT m)) ∧
      shiftedOrientationExpansion H.dS = shiftedOrientationExpansion H.dQ := by
  by_cases hSa : H.dS.edgeData.Admissible ∅
  · exact dnModelsClaim_all n k H.dS t x hSa H.dS_eligible H.dS_bounce H.dS_hx H.dS_hx1
      H.dQ H.dQ_isDNTarget
  · have hQa : ¬ H.dQ.edgeData.Admissible ∅ := fun h => hSa (H.dS_admissible_iff.mpr h)
    refine ⟨fun m => ?_, ?_⟩
    · change xQShift m (H.dS.edgeData.coloringLLT m) = xQShift m (H.dQ.edgeData.coloringLLT m)
      rw [coloringLLT_eq_zero_of_not_admissible_empty _ hSa,
        coloringLLT_eq_zero_of_not_admissible_empty _ hQa]
    · rw [shiftedOrientationExpansion_eq_zero_of_not_admissible_empty _ hSa,
        shiftedOrientationExpansion_eq_zero_of_not_admissible_empty _ hQa]

theorem dN_nn :
    (∀ m : ℕ, xQShift m (H.dN.coloringLLT m) = MvPolynomial.C (Polynomial.X + 1) *
      xQShift m (H.dNs.coloringLLT m)) ∧
    shiftedOrientationExpansion H.dN = MvPolynomial.C (Polynomial.X + 1) *
      shiftedOrientationExpansion H.dNs :=
  shifted_nn_of_counted H.dN H.dN_eligible H.dN_admissible H.dN_bounce H.dN_hx H.dN_hx1

theorem dJ_nn :
    (∀ m : ℕ, xQShift m (H.dJ.coloringLLT m) = MvPolynomial.C (Polynomial.X + 1) *
      xQShift m (H.dJs.coloringLLT m)) ∧
    shiftedOrientationExpansion H.dJ = MvPolynomial.C (Polynomial.X + 1) *
      shiftedOrientationExpansion H.dJs :=
  shifted_nn_of_counted H.dJ H.dJ_eligible H.dJ_admissible H.dJ_bounce H.dJ_hx H.dJ_hx1

section Coloring

variable (m : ℕ)

theorem col_e1 : xQShift m (H.dN.coloringLLT m) =
    MvPolynomial.C Polynomial.X * xQShift m (D.coloringLLT m) +
      xQShift m (H.dE.coloringLLT m) :=
  D.xQShift_coloringLLT_unstrict_corner H.g H.g_mem m

theorem col_e2 : xQShift m (H.dE.coloringLLT m) =
    MvPolynomial.C Polynomial.X * xQShift m (H.dS.coloringLLT m) +
      xQShift m (H.dJ.coloringLLT m) :=
  H.dE.xQShift_coloringLLT_corner H.ell H.ell_corner H.ell_not_mem m

theorem col_e3 : xQShift m (H.dN.coloringLLT m) =
    MvPolynomial.C (Polynomial.X + 1) * xQShift m (H.dNs.coloringLLT m) :=
  H.dN_nn.1 m

theorem col_e4 : xQShift m (H.dJ.coloringLLT m) =
    MvPolynomial.C (Polynomial.X + 1) * xQShift m (H.dJs.coloringLLT m) :=
  H.dJ_nn.1 m

theorem col_e5 : xQShift m (H.dS.coloringLLT m) = xQShift m (H.dQ.coloringLLT m) :=
  H.dS_dQ_models.1 m

theorem col_e6 : xQShift m (H.dNs.coloringLLT m) =
    MvPolynomial.C Polynomial.X * xQShift m (H.dQ.coloringLLT m) +
      xQShift m (H.dEs.coloringLLT m) := by
  rw [H.dNs_eq]
  exact H.dQ.xQShift_coloringLLT_unstrict_corner H.gQ H.gQ_mem m

theorem col_e7 : xQShift m (H.dEs.coloringLLT m) =
    MvPolynomial.C Polynomial.X * xQShift m (H.dR.coloringLLT m) +
      xQShift m (H.dJs.coloringLLT m) := by
  rw [← H.dEs_strictify_eq, ← H.dEs_deleteCorner_eq]
  exact H.dEs.xQShift_coloringLLT_corner H.ellEs H.ellEs_corner H.ellEs_not_mem m

theorem xQShift_coloringLLT_nd : xQShift m (D.coloringLLT m) =
    MvPolynomial.C Polynomial.X * xQShift m (H.dQ.coloringLLT m) +
      MvPolynomial.C (Polynomial.X + 1) * xQShift m (H.dR.coloringLLT m) := by
  have h1 : (MvPolynomial.C (Polynomial.X + 1) : XPoly m) = MvPolynomial.C Polynomial.X + 1 := by
    rw [map_add, map_one]
  have e3 := H.col_e3 m
  have e4 := H.col_e4 m
  rw [h1] at e3 e4 ⊢
  exact nd_cancel (C_X_ne_zero_xPoly m) (H.col_e1 m) (H.col_e2 m) e3 e4 (H.col_e5 m)
    (H.col_e6 m) (H.col_e7 m)

theorem coloringLLT_nd : D.coloringLLT m =
    MvPolynomial.C (Polynomial.X - 1) * H.dQ.coloringLLT m +
      MvPolynomial.C Polynomial.X * H.dR.coloringLLT m := by
  apply xQShift_injective m
  rw [H.xQShift_coloringLLT_nd m, (xQShift m).map_add, (xQShift m).map_mul,
    (xQShift m).map_mul, xQShift_C, xQShift_C, qShift_X, qShift_X_sub_one]

end Coloring

section Expansion

theorem exp_e1 : shiftedOrientationExpansion H.dN =
    MvPolynomial.C Polynomial.X * shiftedOrientationExpansion D +
      shiftedOrientationExpansion H.dE :=
  D.shiftedOrientationExpansion_unstrict_corner H.g H.g_mem

theorem exp_e2 : shiftedOrientationExpansion H.dE =
    MvPolynomial.C Polynomial.X * shiftedOrientationExpansion H.dS +
      shiftedOrientationExpansion H.dJ :=
  H.dE.shiftedOrientationExpansion_corner H.ell H.ell_corner H.ell_not_mem

theorem exp_e6 : shiftedOrientationExpansion H.dNs =
    MvPolynomial.C Polynomial.X * shiftedOrientationExpansion H.dQ +
      shiftedOrientationExpansion H.dEs := by
  rw [H.dNs_eq]
  exact H.dQ.shiftedOrientationExpansion_unstrict_corner H.gQ H.gQ_mem

theorem exp_e7 : shiftedOrientationExpansion H.dEs =
    MvPolynomial.C Polynomial.X * shiftedOrientationExpansion H.dR +
      shiftedOrientationExpansion H.dJs := by
  rw [← H.dEs_strictify_eq, ← H.dEs_deleteCorner_eq]
  exact H.dEs.shiftedOrientationExpansion_corner H.ellEs H.ellEs_corner H.ellEs_not_mem

theorem shiftedOrientationExpansion_nd : shiftedOrientationExpansion D =
    MvPolynomial.C Polynomial.X * shiftedOrientationExpansion H.dQ +
      MvPolynomial.C (Polynomial.X + 1) * shiftedOrientationExpansion H.dR := by
  have h1 : (MvPolynomial.C (Polynomial.X + 1) : EExpansion) =
      MvPolynomial.C Polynomial.X + 1 := by
    rw [map_add, map_one]
  have e3 : shiftedOrientationExpansion H.dN =
      MvPolynomial.C (Polynomial.X + 1) * shiftedOrientationExpansion H.dNs := H.dN_nn.2
  have e4 : shiftedOrientationExpansion H.dJ =
      MvPolynomial.C (Polynomial.X + 1) * shiftedOrientationExpansion H.dJs := H.dJ_nn.2
  rw [h1] at e3 e4 ⊢
  exact nd_cancel C_X_ne_zero_eExpansion H.exp_e1 H.exp_e2 e3 e4 H.dS_dQ_models.2 H.exp_e6
    H.exp_e7

end Expansion

end NDSeparatedHyp

end VerticalStripLLT.Circular.Diagram

namespace VerticalStripLLT.Circular.Diagram

/-- Actual ND reduction when the terminal upper vertex avoids all strict main heads. -/
theorem exists_nd_separated_reduction {n : ℕ} (D : Diagram n) {t x : ℤ} {k : ℕ}
    (ha : D.edgeData.Admissible ∅) (ht : D.EligibleDE t)
    (h : ReverseBounceN D t x k)
    (hx : ¬ D.strictAt x) (hx1 : D.strictAt (x + 1))
    (hsep : ∀ i ≤ k, D.residue (D.boundary^[i] t) ≠ D.residue (x + 1)) :
    ∃ Q R : Diagram n,
      Q.doubledArea + 2 = D.doubledArea ∧
      R.doubledArea + 4 = D.doubledArea ∧
      (∀ m : ℕ, D.coloringLLT m =
        MvPolynomial.C (Polynomial.X - 1) * Q.coloringLLT m +
          MvPolynomial.C Polynomial.X * R.coloringLLT m) ∧
      shiftedOrientationExpansion D =
        MvPolynomial.C Polynomial.X * shiftedOrientationExpansion Q +
          MvPolynomial.C (Polynomial.X + 1) * shiftedOrientationExpansion R := by
  have H : NDSeparatedHyp D t x k := ⟨ha, ht, h, hx, hx1, hsep⟩
  exact ⟨H.dQ, H.dR, H.dQ_doubledArea, H.dR_doubledArea, H.coloringLLT_nd,
    H.shiftedOrientationExpansion_nd⟩

end VerticalStripLLT.Circular.Diagram
