import VerticalStripLLT.Components.DiagramProof.BlockReordering

/-!
# Smaller certificates for components without a witness

A component either omits a maximal corner, or has disconnected selected
relation, or selects every maximal corner with connected relation. In the last
case, if no state has all maximal corners covering, alternating deletion
applies. Thus every component of a naturally connected diagram which contains
no connected common-cover state has a signed certificate by smaller whole
components, with the same coefficients for both right-marked values.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- The component of `θ` contains a connected common-cover state. -/
def HasCommonWitness (θ : Orientation D) : Prop :=
  ∃ η ∈ flipComponent D θ, SelectedConnected η ∧ (allCorners D).CommonCover η

variable {k : ℕ} {D : Diagram (k + 1)} (hD : Forward D)

/-- **Component corrections.** -/
theorem certifies_of_not_hasCommonWitness
    (hconn : ∀ u v, Relation.EqvGen (naturalRel D) u v) (θ : Orientation D)
    (hno : ¬ HasCommonWitness θ) : ∃ c : Cert k, Certifies ⟨D, hD, θ⟩ c := by
  by_cases hall : ∀ s t, MaximalPair (naturalRel D) s t → D.edgeData.selected θ.val s t
  · by_cases hcθ : SelectedConnected θ
    · apply certifies_noCommonCover hD θ hall
      intro η hη hcov
      exact hno ⟨η, hη, (selectedConnected_iff_of_reachable (mem_flipComponent_iff.mp hη)).mp
        hcθ, hcov⟩
    · exact certifies_disconnected hD θ hconn hcθ
  · push Not at hall
    obtain ⟨s, t, hmax, hsel⟩ := hall
    exact certifies_absentCorner hD θ hmax hsel

end

end VerticalStripLLT.Circular.DiagramProof
