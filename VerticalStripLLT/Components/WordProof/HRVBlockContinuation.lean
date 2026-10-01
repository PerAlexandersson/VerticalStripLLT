import VerticalStripLLT.Components.WordProof.BlockContinuation
import VerticalStripLLT.Components.WordProof.HRVSupportDifference

/-! Signed first-block cancellation forces the next actual HRV fiber. -/

namespace VerticalStripLLT.Circular.Orientation

open Classical
open scoped BigOperators
open VerticalStripLLT.Components

variable {n : ℕ} {D : Diagram n} {K : Type*} [CommRing K]

/-- At an HRV threshold, the only surviving first block is the next actual fiber. -/
theorem signed_blockContinuation_hrvInitialSupport (θ : Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (U : Finset (Fin n)) (r : Fin n) (hr : r ∈ U)
    (hmax : ∀ v ∈ U, v ≤ r) (w : List (Fin n)) :
    (∑ T ∈ (U.erase r).powerset, (-1 : K) ^ T.card *
      if fullOn (θ.hrvInitialSupport (r.val + 1)) (blockWord U T ++ w) ∧
          wordCompatible (D.edgeData.selected θ.val) (blockWord U T ++ w)
        then 1 else 0) =
      if U = Finset.univ.filter (fun v => θ.hrv v = r) then
        if fullOn (θ.hrvInitialSupport r.val) w ∧
          wordCompatible (D.edgeData.selected θ.val) w then 1 else 0
      else 0 := by
  rw [signed_blockContinuation_scalar (D.edgeData.selected θ.val)
    (fun {_ _} h => θ.selected_lt_of_forward hforward h)
    (θ.hrvInitialSupport (r.val + 1)) U r hr hmax w]
  by_cases hU : U = Finset.univ.filter (fun v => θ.hrv v = r)
  · subst U
    have hsub := θ.hrvFiber_subset_hrvInitialSupport_succ hforward r
    have hcross := θ.no_selected_edge_hrvInitialSupport_to_hrvFiber hforward r
    have hunique := θ.hrvFiber_unique_induced_sink hforward r hr
    rw [θ.hrvInitialSupport_sdiff_hrvFiber hforward r]
    split_ifs <;> grind
  · rw [ite_eq_right hU]
    have hnot : ¬(U ⊆ θ.hrvInitialSupport (r.val + 1) ∧
        fullOn (θ.hrvInitialSupport (r.val + 1) \ U) w ∧
        wordCompatible (D.edgeData.selected θ.val) w ∧
        (∀ x ∈ θ.hrvInitialSupport (r.val + 1) \ U, ∀ y ∈ U,
          ¬ D.edgeData.selected θ.val x y) ∧
        (∀ v ∈ U, sinkOn (D.edgeData.selected θ.val) U v ↔ v = r)) := by
      rintro ⟨hsub, _, _, hcross, hunique⟩
      apply hU
      apply θ.block_eq_hrvFiber_of_initialSupport hforward U r hr hsub hmax
      · intro v hv hne hs
        exact hne ((hunique v hv).mp hs)
      · intro x hx y hy hxy
        by_contra hxU
        exact hcross x (Finset.mem_sdiff.mpr ⟨hx, hxU⟩) y hy hxy
    exact ite_eq_right hnot

end VerticalStripLLT.Circular.Orientation
