import VerticalStripLLT.Circular.HRV

/-! Sink and idempotence properties of circular highest-reachable vertices. -/

namespace VerticalStripLLT.Circular

namespace Orientation

variable {n : ℕ} {D : Diagram n}

theorem no_liftStep_from_liftedHRV (θ : Orientation D) (z w : ℤ)
    (hstep : D.liftStep θ.val (θ.liftedHRV z) w) : False := by
  have hreach := θ.liftedHRV_reachable z
  have hcombined := Relation.ReflTransGen.tail hreach hstep
  have hle := θ.le_liftedHRV_of_reachable hcombined
  have hpos := (D.liftStep_bounds hstep).1
  lia

theorem residue_intCast_eq (v : Fin n) : D.residue (v.val : ℤ) = v := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [D.residue_coe_val]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast v.isLt)

theorem hrv_is_sink (θ : Orientation D) (v : Fin n) (w : Fin n)
    (h : D.edgeData.selected θ.val (θ.hrv v) w) : False := by
  rcases h with ⟨e, he, htail, hhead⟩
  apply θ.no_liftStep_from_liftedHRV (v.val : ℤ)
  refine ⟨e, he, ?_, rfl⟩
  exact htail.symm

theorem hrv_fixes_sink (θ : Orientation D) (v : Fin n)
    (hsink : ∀ w, ¬ D.edgeData.selected θ.val v w) : θ.hrv v = v := by
  have hreach_eq : ∀ w, Relation.ReflTransGen (D.liftStep θ.val)
      (v.val : ℤ) w → w = (v.val : ℤ) := by
    intro w hpath
    induction hpath with
    | refl => rfl
    | tail _ hstep ih =>
      have hselected := D.liftStep_selected hstep
      rw [ih] at hselected
      rw [residue_intCast_eq] at hselected
      exact (hsink _ hselected).elim
  have hmax := θ.liftedHRV_reachable (v.val : ℤ)
  have hmax_eq := hreach_eq _ hmax
  unfold hrv
  rw [hmax_eq, residue_intCast_eq]

theorem hrv_idempotent (θ : Orientation D) (v : Fin n) :
    θ.hrv (θ.hrv v) = θ.hrv v := by
  exact θ.hrv_fixes_sink (θ.hrv v) (fun w h => θ.hrv_is_sink _ _ h)

end Orientation
end VerticalStripLLT.Circular
