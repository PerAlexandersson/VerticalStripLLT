import VerticalStripLLT.Components.CompatibleDiagramOrientations
import VerticalStripLLT.Components.BalancedHRVTransport
import VerticalStripLLT.Components.SelectedColoringTransport
import VerticalStripLLT.Circular.ComponentSemantics

/-! Actual component valuations transported to a set of ordinary orientations. -/

namespace VerticalStripLLT.Circular.Diagram

open Classical
open scoped BigOperators

noncomputable section

variable {n : ℕ} (D : Diagram n) (q : Fin n → ℤ) (σ : Fin n ≃ Fin n)
variable (hmono : StrictMono (q ∘ σ)) (hq : ∀ v, D.residue (q v) = v)
variable (hstrict : D.strict = ∅)

/-- The ordinary orientation map is injective before restricting to components. -/
theorem orientationFromCompatible_injective :
    Function.Injective (D.orientationFromCompatible q σ hmono hq hstrict) := by
  exact Function.LeftInverse.injective
    (D.orientationToCompatible_fromCompatible q σ hmono hq hstrict)

theorem orientationFromCompatible_hrvMonomial
    (η : Orientation (D.compatibleDiagram q σ hmono)) :
    (D.orientationFromCompatible q σ hmono hq hstrict η).hrvMonomial = η.hrvMonomial := by
  exact Orientation.hrvMonomial_eq_of_balanced_relabel _ η
    (D.compatibleDiagram_forward q σ hmono) hq
    (D.orientationFromCompatible_balancedPotential q σ hmono hq hstrict η)
    σ hmono (D.orientationFromCompatible_selected q σ hmono hq hstrict η)

theorem orientationFromCompatible_strictOrderEnumerator
    (η : Orientation (D.compatibleDiagram q σ hmono)) (m : ℕ) :
    D.edgeData.strictOrderEnumerator
      (D.orientationFromCompatible q σ hmono hq hstrict η).val m =
        (D.compatibleDiagram q σ hmono).edgeData.strictOrderEnumerator η.val m := by
  exact (Components.strictOrderEnumerator_selected_relabel _ η σ
    (D.orientationFromCompatible_selected q σ hmono hq hstrict η) m).symm

/-- All ordinary states whose images belong to the chosen original component. -/
def compatibleComponentPreimage (θ : Orientation D) :
    Finset (Orientation (D.compatibleDiagram q σ hmono)) :=
  Finset.univ.filter fun η =>
    D.orientationFromCompatible q σ hmono hq hstrict η ∈ flipComponent D θ

/-- Recovery is needed only statewise; the preimage need not be one ordinary component. -/
theorem compatibleComponentPreimage_image (θ : Orientation D)
    (hp : D.naturalGain.BalancedPotential (D.strict ∪ θ.val) q) :
    (D.compatibleComponentPreimage q σ hmono hq hstrict θ).image
      (D.orientationFromCompatible q σ hmono hq hstrict) = flipComponent D θ := by
  ext α
  constructor
  · intro h
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hη).2
  · intro hα
    have hpα := (balancedPotential_iff_of_reachable q (mem_flipComponent_iff.mp hα)).mp hp
    have hrec := D.orientationFromCompatible_toCompatible q σ hmono hq hstrict α hpα
    apply Finset.mem_image.mpr
    refine ⟨D.orientationToCompatible q σ hmono α, ?_, hrec⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrec.symm ▸ hα⟩

theorem componentStrictEnumerator_eq_preimage_sum (θ : Orientation D)
    (hp : D.naturalGain.BalancedPotential (D.strict ∪ θ.val) q) (m : ℕ) :
    componentStrictEnumerator D θ m =
      ∑ η ∈ D.compatibleComponentPreimage q σ hmono hq hstrict θ,
        (D.compatibleDiagram q σ hmono).edgeData.strictOrderEnumerator η.val m := by
  simp only [componentStrictEnumerator,
    ← D.compatibleComponentPreimage_image q σ hmono hq hstrict θ hp,
    Finset.sum_image (D.orientationFromCompatible_injective q σ hmono hq hstrict).injOn,
    D.orientationFromCompatible_strictOrderEnumerator]

theorem componentHRV_eq_preimage_sum (θ : Orientation D)
    (hp : D.naturalGain.BalancedPotential (D.strict ∪ θ.val) q) :
    componentHRV D θ =
      ∑ η ∈ D.compatibleComponentPreimage q σ hmono hq hstrict θ, η.hrvMonomial := by
  simp only [componentHRV,
    ← D.compatibleComponentPreimage_image q σ hmono hq hstrict θ hp,
    Finset.sum_image (D.orientationFromCompatible_injective q σ hmono hq hstrict).injOn,
    D.orientationFromCompatible_hrvMonomial]

end

end VerticalStripLLT.Circular.Diagram
