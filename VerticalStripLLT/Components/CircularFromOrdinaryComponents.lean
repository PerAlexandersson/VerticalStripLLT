import VerticalStripLLT.Components.CompatibleDiagramSemantics
import VerticalStripLLT.Components.CompatibleDiagramFlips
import VerticalStripLLT.Components.FlipClosedSums
import VerticalStripLLT.Components.ComponentBalancedReduction

/-! Reducing the full circular component identity to the ordinary component identity. -/

namespace VerticalStripLLT.Circular

open Classical
open scoped BigOperators

variable {n : ℕ} {D : Diagram n}

namespace Diagram

variable (D) (q : Fin n → ℤ) (σ : Fin n ≃ Fin n)
variable (hmono : StrictMono (q ∘ σ)) (hq : ∀ v, D.residue (q v) = v)
variable (hstrict : D.strict = ∅)

/-- The ordinary preimage is a union of complete ordinary components. -/
theorem compatibleComponentPreimage_closed (θ : Orientation D)
    {η ζ : Orientation (D.compatibleDiagram q σ hmono)}
    (hη : η ∈ D.compatibleComponentPreimage q σ hmono hq hstrict θ)
    (h : Flip (D.compatibleDiagram q σ hmono) η ζ) :
    ζ ∈ D.compatibleComponentPreimage q σ hmono hq hstrict θ := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact mem_flipComponent_iff.mpr
    ((mem_flipComponent_iff.mp (Finset.mem_filter.mp hη).2).tail
      (D.flipFromCompatible q σ hmono hq hstrict h))

include hq hstrict in
/-- Only the ordinary component identity remains as a semantic input. -/
theorem component_identity_of_compatible_components (θ : Orientation D)
    (hp : D.naturalGain.BalancedPotential (D.strict ∪ θ.val) q) (m : ℕ)
    (hordinary : ∀ η : Orientation (D.compatibleDiagram q σ hmono),
      componentStrictEnumerator (D.compatibleDiagram q σ hmono) η m =
        evalElementary m (componentHRV (D.compatibleDiagram q σ hmono) η)) :
    componentStrictEnumerator D θ m = evalElementary m (componentHRV D θ) := by
  rw [D.componentStrictEnumerator_eq_preimage_sum q σ hmono hq hstrict θ hp m,
    D.componentHRV_eq_preimage_sum q σ hmono hq hstrict θ hp]
  simp only [map_sum]
  apply sum_eq_of_flipComponent_sum_eq_of_closed
    (D.compatibleComponentPreimage q σ hmono hq hstrict θ)
    (fun η hη ζ h => D.compatibleComponentPreimage_closed q σ hmono hq hstrict θ hη h)
  intro η
  simpa only [componentStrictEnumerator, componentHRV, map_sum] using hordinary η

end Diagram

/-- The general circular theorem follows from the theorem on all forward diagrams.
The hypothesis is explicit: this reduction does not assert that the remaining
ordinary component identity has already been proved. -/
theorem component_identity_of_forward_components (γ : Orientation D) (m : ℕ)
    (hordinary : ∀ {k : ℕ} (E : Diagram k),
      (∀ e : Edge E.area, e.tail < e.head) → ∀ η : Orientation E,
        componentStrictEnumerator E η m = evalElementary m (componentHRV E η)) :
    componentStrictEnumerator D γ m = evalElementary m (componentHRV D γ) := by
  apply component_identity_of_undecorated_balanced_components γ m
  intro θ hθ
  obtain ⟨q, hq, hp, hinj⟩ := D.undecorated.exists_injective_balancedLifts hθ
  obtain ⟨σ, hmono⟩ := Diagram.exists_increasing_liftOrder q hinj
  exact D.undecorated.component_identity_of_compatible_components q σ hmono hq rfl θ hp m
    (hordinary _ (D.undecorated.compatibleDiagram_forward q σ hmono))

end VerticalStripLLT.Circular
