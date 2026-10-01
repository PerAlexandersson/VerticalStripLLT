import VerticalStripLLT.Components.DiagramProof.ComponentCorrections
import VerticalStripLLT.Components.DiagramProof.CommonCoverUniqueness
import VerticalStripLLT.Components.DiagramProof.DNRecurrence

/-!
# Isolating one whole component in a full layer

Partition an edge layer into whole components. If exactly one of them contains a
connected common-cover state, every other component has a smaller certificate by
the component corrections. A full-layer identity therefore certifies the
distinguished component:

    X(C) = X(layer) - sum_(D ≠ C) X(D),   X = K, E,

with the same integer coefficients for both values. The NN and DN layer
identities supply the right-hand layer as whole components of a smaller target.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k : ℕ} {D : Diagram (k + 1)} (hD : Forward D)

/-- **Component isolation.** -/
theorem certifies_of_layer (hconn : ∀ u v, Relation.EqvGen (naturalRel D) u v)
    (huniq : CommonCoverUnique D) (θ : Orientation D) (hθ : HasCommonWitness θ)
    (c₀ : Cert k)
    (hc₀ : ∀ m β, layerK D (Fin.last k) (totalSelected θ) m β = Cert.K c₀ m β ∧
      layerE D (Fin.last k) (totalSelected θ) m β = Cert.E c₀ m β)
    (hsmall : Cert.Smaller c₀ D) : ∃ c : Cert k, Certifies ⟨D, hD, θ⟩ c := by
  let S := edgeLayer D (totalSelected θ)
  obtain ⟨R, hRS, hRdisj, hSR⟩ := exists_component_reps S (edgeLayer_closed _)
  have hθS : θ ∈ S := mem_edgeLayer.mpr rfl
  obtain ⟨r₀, hr₀, hθr₀⟩ : ∃ r₀ ∈ R, θ ∈ flipComponent D r₀ := by
    have := hθS
    rw [hSR, Finset.mem_biUnion] at this
    exact this
  have hcomp₀ : flipComponent D r₀ = flipComponent D θ := (flipComponent_eq_of_mem hθr₀).symm
  -- Every other representative has no witness.
  have hnone : ∀ r ∈ R.erase r₀, ¬ HasCommonWitness r := by
    intro r hr ⟨η, hη, hcη, hccη⟩
    obtain ⟨η₀, hη₀, hc₀η, hcc₀η⟩ := hθ
    have hrS : r ∈ S := hRS (Finset.mem_of_mem_erase hr)
    have htot : totalSelected η₀ = totalSelected η := by
      have h1 := mem_edgeLayer.mp (flipComponent_subset_edgeLayer hθS hη₀)
      have h2 := mem_edgeLayer.mp (flipComponent_subset_edgeLayer hrS hη)
      rw [h1, h2]
    have hpath := huniq η₀ η hcc₀η hccη hc₀η hcη htot
    have hηθ : η ∈ flipComponent D θ :=
      mem_flipComponent_iff.mpr ((mem_flipComponent_iff.mp hη₀).trans hpath)
    have hne : r ≠ r₀ := Finset.ne_of_mem_erase hr
    have := hRdisj (Finset.mem_of_mem_erase hr) hr₀ hne
    rw [Function.onFun, Finset.disjoint_left] at this
    exact this hη (hcomp₀ ▸ hηθ)
  have hcorr (r : Orientation D) (hr : r ∈ R.erase r₀) :
      ∃ c : Cert k, Certifies ⟨D, hD, r⟩ c :=
    certifies_of_not_hasCommonWitness hD hconn r (hnone r hr)
  let cr : Orientation D → Cert k := fun r =>
    if hr : r ∈ R.erase r₀ then Classical.choose (hcorr r hr) else 0
  have hcr (r : Orientation D) (hr : r ∈ R.erase r₀) : Certifies ⟨D, hD, r⟩ (cr r) := by
    simp only [cr, hr, dite_true]
    exact Classical.choose_spec (hcorr r hr)
  refine ⟨c₀ - ∑ r ∈ R.erase r₀, cr r, fun m β => ⟨?_, ?_⟩, ?_⟩
  · have hlayer : layerK D (Fin.last k) (totalSelected θ) m β =
        componentMarkedK θ (Fin.last k) m β +
          ∑ r ∈ R.erase r₀, componentMarkedK r (Fin.last k) m β := by
      unfold layerK
      rw [sum_eq_sum_component_reps hRdisj hSR, ← Finset.add_sum_erase _ _ hr₀]
      unfold componentMarkedK
      rw [hcomp₀]
    have hrest : ∑ r ∈ R.erase r₀, Cert.K (cr r) m β =
        ∑ r ∈ R.erase r₀, componentMarkedK r (Fin.last k) m β :=
      Finset.sum_congr rfl fun r hr => (((hcr r hr).1 m β).1).symm
    rw [Cert.K_sub, Cert.K_sum, ← (hc₀ m β).1, hlayer, hrest, add_sub_cancel_right]
    rfl
  · have hlayer : layerE D (Fin.last k) (totalSelected θ) m β =
        componentMarkedE θ (Fin.last k) m β +
          ∑ r ∈ R.erase r₀, componentMarkedE r (Fin.last k) m β := by
      unfold layerE
      rw [sum_eq_sum_component_reps hRdisj hSR, ← Finset.add_sum_erase _ _ hr₀]
      unfold componentMarkedE
      rw [hcomp₀]
    have hrest : ∑ r ∈ R.erase r₀, Cert.E (cr r) m β =
        ∑ r ∈ R.erase r₀, componentMarkedE r (Fin.last k) m β :=
      Finset.sum_congr rfl fun r hr => (((hcr r hr).1 m β).2).symm
    rw [Cert.E_sub, Cert.E_sum, ← (hc₀ m β).2, hlayer, hrest, add_sub_cancel_right]
    rfl
  · exact Cert.smaller_sub hsmall (Cert.smaller_sum fun r hr => (hcr r hr).2)

/-- **NN certificate.** A connected common-cover component at an NN contact. -/
theorem certifies_nn (hconn : ∀ u v, Relation.EqvGen (naturalRel D) u v)
    (huniq : CommonCoverUnique D) (θ : Orientation D) (hθ : HasCommonWitness θ)
    {x y t : Fin (k + 1)} (h : NNContact D x y t) : ∃ c : Cert k, Certifies ⟨D, hD, θ⟩ c := by
  have hR := nnTarget_forward hD h
  obtain ⟨s, hs⟩ : ∃ s, totalSelected θ = s + 1 := by
    refine ⟨totalSelected θ - 1, ?_⟩
    have : 0 < totalSelected θ := by
      rw [totalSelected_eq_card_selected]
      exact Finset.card_pos.mpr ⟨(x, t), by
        simpa using selected_of_strictRel θ h.root⟩
    lia
  apply certifies_of_layer hD hconn huniq θ hθ
    (layerCert hR _ (edgeLayer_closed (s + 1)) + layerCert hR _ (edgeLayer_closed s))
  · intro m β
    rw [hs, Cert.K_add, Cert.E_add, ← layerCert_K, ← layerCert_K, ← layerCert_E,
      ← layerCert_E]
    exact h.layer hD s m β
  · exact Cert.smaller_add (layerCert_smaller hR _ _ (h.target_measureLT hD))
      (layerCert_smaller hR _ _ (h.target_measureLT hD))

/-- **DN certificate.** A connected common-cover component at a DN contact. -/
theorem certifies_dn (hconn : ∀ u v, Relation.EqvGen (naturalRel D) u v)
    (huniq : CommonCoverUnique D) (θ : Orientation D) (hθ : HasCommonWitness θ)
    {u x y t : Fin (k + 1)} (h : DNContact D u x y t) :
    ∃ c : Cert k, Certifies ⟨D, hD, θ⟩ c := by
  have hR := dnTarget_forward hD h
  apply certifies_of_layer hD hconn huniq θ hθ
    (layerCert hR _ (edgeLayer_closed (totalSelected θ)))
  · intro m β
    rw [← layerCert_K, ← layerCert_E]
    exact h.layer hD _ m β
  · exact layerCert_smaller hR _ _ (h.target_measureLT hD)

end

end VerticalStripLLT.Circular.DiagramProof
