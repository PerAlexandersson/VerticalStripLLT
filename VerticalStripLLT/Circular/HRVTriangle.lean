import VerticalStripLLT.Circular.HRVStepComparison
import VerticalStripLLT.Circular.FirstBounceOrientationIdentity
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

section Triangle

variable {s g1 g2 : Edge D.area} {P Y T : ℤ}
  (hs : s ∈ D.strict) (hsL : D.naturalLift s P T)
  (h1L : D.naturalLift g1 P Y) (h2L : D.naturalLift g2 Y T)

include hs hsL in
theorem tri_s_step (A : Finset (Edge D.area)) : D.liftStep A P T :=
  ⟨s, Finset.mem_union_left _ hs, hsL.1, hsL.2⟩

include h2L hs hsL in
theorem tri_caseI_key (θ0 θ1 : Orientation D) (hsub : θ0.val ⊆ θ1.val)
    (hval : ∀ ε ∈ θ1.val, ε ∉ θ0.val → ε = g2)
    (hc : θ0.liftedHRV Y ≤ θ0.liftedHRV P) :
    θ1.liftedHRV Y ≤ θ1.liftedHRV P := by
  have hw := θ1.liftedHRV_reachable Y
  rcases reflTransGen_firstUse (R := D.liftStep θ0.val)
      (F := fun x y => D.residue x = g2.tail ∧ y = x + g2.length.val) (fun x y h => by
        rcases h with ⟨ε, hε, hx, hy⟩
        by_cases h0 : ε ∈ D.strict ∪ θ0.val
        · exact Or.inl ⟨ε, h0, hx, hy⟩
        · right
          have hεθ1 : ε ∈ θ1.val := by
            rcases Finset.mem_union.mp hε with h | h
            · exact absurd (Finset.mem_union_left _ h) h0
            · exact h
          have heq := hval ε hεθ1 (fun h => h0 (Finset.mem_union_right _ h))
          subst heq
          exact ⟨hx, hy⟩) hw with h | ⟨c, c', h1, ⟨hc1, hc2⟩, h3⟩
  · calc θ1.liftedHRV Y ≤ θ0.liftedHRV Y := θ0.le_liftedHRV_of_reachable h
      _ ≤ θ0.liftedHRV P := hc
      _ ≤ θ1.liftedHRV P := θ0.liftedHRV_mono_of_subset θ1 hsub _
  · have hcY : c = Y := by
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp h1 with h | h
      · exact h
      · exfalso
        apply θ0.no_lifted_cycle h
        rw [hc1, h2L.1]
    rw [hc2, hcY, ← h2L.2] at h3
    calc θ1.liftedHRV Y ≤ θ1.liftedHRV T := θ1.le_liftedHRV_of_reachable h3
      _ ≤ θ1.liftedHRV P := θ1.liftedHRV_le_of_step (D.tri_s_step hs hsL _)

include h1L hs hsL in
theorem tri_caseII_key (θ0 θ2 : Orientation D)
    (hval : ∀ ε ∈ θ2.val, ε ∉ θ0.val → ε = g1) :
    θ2.liftedHRV T ≤ θ0.liftedHRV T := by
  have hw := θ2.liftedHRV_reachable T
  rcases reflTransGen_firstUse (R := D.liftStep θ0.val)
      (F := fun x y => D.residue x = g1.tail ∧ y = x + g1.length.val) (fun x y h => by
        rcases h with ⟨ε, hε, hx, hy⟩
        by_cases h0 : ε ∈ D.strict ∪ θ0.val
        · exact Or.inl ⟨ε, h0, hx, hy⟩
        · right
          have hεθ2 : ε ∈ θ2.val := by
            rcases Finset.mem_union.mp hε with h | h
            · exact absurd (Finset.mem_union_left _ h) h0
            · exact h
          have heq := hval ε hεθ2 (fun h => h0 (Finset.mem_union_right _ h))
          subst heq
          exact ⟨hx, hy⟩) hw with h | ⟨c, c', h1, ⟨hc1, _⟩, _⟩
  · exact θ0.le_liftedHRV_of_reachable h
  · exfalso
    have hcs : D.residue c = s.tail := hc1.trans (h1L.1.symm.trans hsL.1)
    have hstep : D.liftStep θ0.val c (c + s.length.val) :=
      ⟨s, Finset.mem_union_left _ hs, hcs, rfl⟩
    apply θ0.no_lifted_cycle (Relation.TransGen.tail' h1 hstep)
    rw [D.residue_add_length s c hcs, D.naturalLift_head hsL]

include hs hsL h1L h2L in
theorem tri_local_identity (hg1 : g1 ∈ D.edgeData.normalEdges)
    (hg2 : g2 ∈ D.edgeData.normalEdges) (θ : Finset (Edge D.area))
    (hθ : θ ⊆ D.edgeData.normalEdges) :
    D.orientMono (insert g1 θ) + D.orientMono (insert g2 θ) =
      D.orientMono θ + D.orientMono (insert g2 (insert g1 θ)) := by
  have hN01 : insert g1 θ ⊆ D.edgeData.normalEdges := Finset.insert_subset hg1 hθ
  have hN10 : insert g2 θ ⊆ D.edgeData.normalEdges := Finset.insert_subset hg2 hθ
  have hN11 : insert g2 (insert g1 θ) ⊆ D.edgeData.normalEdges :=
    Finset.insert_subset hg2 hN01
  have hcomm : insert g2 (insert g1 θ) = insert g1 (insert g2 θ) :=
    Finset.insert_comm _ _ _
  by_cases h0 : D.edgeData.Admissible θ
  swap
  · have hz : ∀ A, θ ⊆ A → D.orientMono A = 0 := fun A hA =>
      D.orientMono_of_not_adm (fun h => h0 (D.admissible_mono hA h))
    rw [hz _ (Finset.subset_insert _ _), hz _ (Finset.subset_insert _ _),
      hz _ (Finset.Subset.refl _),
      hz _ ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))]
  let θ0 : Orientation D := ⟨θ, hθ, h0⟩
  have hθ0 : D.orientMono θ = θ0.hrvMonomial := D.orientMono_orientation θ0
  have heP : θ0.liftedHRV T ≤ θ0.liftedHRV P :=
    θ0.liftedHRV_le_of_step (D.tri_s_step hs hsL _)
  by_cases hc : θ0.liftedHRV Y ≤ θ0.liftedHRV P
  · have hg : D.orientMono (insert g1 θ) = θ0.hrvMonomial := by
      apply D.orientMono_noop θ0 _ hN01 (Finset.subset_insert _ _)
      intro ε hε hεθ
      rcases Finset.mem_insert.mp hε with rfl | h
      · exact ⟨P, h1L.1, by rw [← h1L.2]; exact hc⟩
      · exact absurd h hεθ
    have hf : D.orientMono (insert g2 θ) =
        D.orientMono (insert g2 (insert g1 θ)) := by
      by_cases h1 : D.edgeData.Admissible (insert g2 θ)
      · let θ1 : Orientation D := ⟨_, hN10, h1⟩
        rw [D.orientMono_orientation θ1, hcomm]
        symm
        apply D.orientMono_noop θ1 _ (hcomm ▸ hN11) (Finset.subset_insert _ _)
        intro ε hε hεθ
        rcases Finset.mem_insert.mp hε with rfl | h
        · refine ⟨P, h1L.1, ?_⟩
          rw [← h1L.2]
          apply D.tri_caseI_key hs hsL h2L θ0 θ1
            (Finset.subset_insert _ _) _ hc
          intro ε hε hεθ
          rcases Finset.mem_insert.mp hε with h | h
          · exact h
          · exact absurd h hεθ
        · exact absurd h hεθ
      · rw [D.orientMono_of_not_adm h1, D.orientMono_of_not_adm
          (fun h => h1 (D.admissible_mono (by
            rw [hcomm]
            exact Finset.subset_insert _ _) h))]
    rw [hg, hf, hθ0, add_comm]
  · push Not at hc
    have hf : D.orientMono (insert g2 θ) = θ0.hrvMonomial := by
      apply D.orientMono_noop θ0 _ hN10 (Finset.subset_insert _ _)
      intro ε hε hεθ
      rcases Finset.mem_insert.mp hε with rfl | h
      · refine ⟨Y, h2L.1, ?_⟩
        rw [← h2L.2]
        lia
      · exact absurd h hεθ
    have hg : D.orientMono (insert g1 θ) =
        D.orientMono (insert g2 (insert g1 θ)) := by
      by_cases h2 : D.edgeData.Admissible (insert g1 θ)
      · let θ2 : Orientation D := ⟨_, hN01, h2⟩
        rw [D.orientMono_orientation θ2]
        symm
        apply D.orientMono_noop θ2 _ hN11 (Finset.subset_insert _ _)
        intro ε hε hεθ
        rcases Finset.mem_insert.mp hε with rfl | h
        · refine ⟨Y, h2L.1, ?_⟩
          rw [← h2L.2]
          have k2 := D.tri_caseII_key hs hsL h1L θ0 θ2 (by
            intro ε hε hεθ
            rcases Finset.mem_insert.mp hε with h | h
            · exact h
            · exact absurd h hεθ)
          have k3 := θ0.liftedHRV_mono_of_subset θ2
            (Finset.subset_insert _ _) Y
          lia
        · exact absurd h hεθ
      · rw [D.orientMono_of_not_adm h2, D.orientMono_of_not_adm
          (fun h => h2 (D.admissible_mono (Finset.subset_insert _ _) h))]
    rw [hg, hf, hθ0, add_comm]

end Triangle
end Diagram
end VerticalStripLLT.Circular
