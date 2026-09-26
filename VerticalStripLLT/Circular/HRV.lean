import VerticalStripLLT.Circular.LiftStep
import VerticalStripLLT.Circular.ReachabilityTranslation
import VerticalStripLLT.Circular.ReachabilityBound

/-! Circular highest-reachable vertices from the actual integer cover. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

variable {n : ℕ}

/-- Ascending non-strict edge sets whose selected relation is acyclic. -/
def Orientation (D : Diagram n) :=
  {A : Finset (Edge D.area) // A ⊆ D.edgeData.normalEdges ∧ D.edgeData.Admissible A}

noncomputable instance (D : Diagram n) : Fintype (Orientation D) := by
  unfold Orientation
  infer_instance

namespace Orientation

variable {D : Diagram n}

theorem reachable_bounds (θ : Orientation D) {z w : ℤ}
    (h : Relation.ReflTransGen (D.liftStep θ.val) z w) :
    z ≤ w ∧ w - z ≤ (((n - 1) ^ 2 : ℕ) : ℤ) := by
  simpa only [Nat.cast_pow] using
    projected_reachable_bounds (D.edgeData.selected θ.val) θ.property.2
      (D.liftStep θ.val) D.residue (fun h => D.liftStep_selected h)
      (fun h => D.liftStep_bounds h) h

/-- The maximum reachable integer lift; the bound is proved for every orientation. -/
noncomputable def liftedHRV (θ : Orientation D) (z : ℤ) : ℤ :=
  reachableMaximum (D.liftStep θ.val) ((n - 1) ^ 2) z

theorem liftedHRV_reachable (θ : Orientation D) (z : ℤ) :
    Relation.ReflTransGen (D.liftStep θ.val) z (θ.liftedHRV z) :=
  maximum_reachable _ _ _

theorem le_liftedHRV_of_reachable (θ : Orientation D) {z w : ℤ}
    (h : Relation.ReflTransGen (D.liftStep θ.val) z w) : w ≤ θ.liftedHRV z :=
  reachable_le_maximum _ _ _ _ (fun _ h => θ.reachable_bounds h) h

/-- This is a greatest reachable vertex, not merely a maximum after arbitrary truncation. -/
theorem isGreatest_liftedHRV (θ : Orientation D) (z : ℤ) :
    IsGreatest {w | Relation.ReflTransGen (D.liftStep θ.val) z w} (θ.liftedHRV z) :=
  ⟨θ.liftedHRV_reachable z, fun _ h => θ.le_liftedHRV_of_reachable h⟩

theorem liftedHRV_translate (θ : Orientation D) (z k : ℤ) :
    θ.liftedHRV (z + (n : ℤ) * k) = θ.liftedHRV z + (n : ℤ) * k := by
  exact reachableMaximum_translate (D.liftStep θ.val) ((n - 1) ^ 2) ((n : ℤ) * k) z
    (fun x y => D.liftStep_translate_iff x y k)

/-- Project the maximum reachable lift, rather than maximizing residue labels. -/
noncomputable def hrv (θ : Orientation D) (u : Fin n) : Fin n :=
  D.residue (θ.liftedHRV (u.val : ℤ))

theorem residue_liftedHRV_eq_hrv (θ : Orientation D) (z : ℤ) :
    D.residue (θ.liftedHRV z) = θ.hrv (D.residue z) := by
  have hz : z = ((D.residue z).val : ℤ) + (n : ℤ) * (z / n) := by
    rw [D.residue_coe_val]
    exact (Int.emod_add_mul_ediv z n).symm
  have h := congrArg (fun t => D.residue (θ.liftedHRV t)) hz
  rw [θ.liftedHRV_translate, D.residue_add_period] at h
  exact h

/-- The formal elementary monomial indexed by the nonempty circular HRV fibers. -/
noncomputable def hrvMonomial (θ : Orientation D) : EExpansion :=
  ∏ r : Fin n,
    if h : 0 < (Finset.univ.filter fun u => θ.hrv u = r).card then
      elementary ⟨(Finset.univ.filter fun u => θ.hrv u = r).card, h⟩
    else 1

end Orientation

/-- Independently defined circular HRV expansion. Equality with LLT remains a theorem target. -/
noncomputable def shiftedOrientationExpansion (D : Diagram n) : EExpansion :=
  ∑ θ : Orientation D,
    MvPolynomial.C (Polynomial.X ^ θ.val.card) * θ.hrvMonomial

end VerticalStripLLT.Circular
