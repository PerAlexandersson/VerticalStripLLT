import VerticalStripLLT.Components.DiagramProof.OverlappingPositions
import VerticalStripLLT.Components.DiagramProof.GoodEdges

/-! Rearranging extra edges through a shared position, keeping the fixed edges at endpoints. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hD : Forward D)

/-- Local exact exchanges in two overlapping pools connect fixed-size anchors
containing the same fixed edges. Intermediate orientations need not retain those edges. -/
theorem anchors_connected_of_overlapping_extra_positions
    (T J K : Finset (Edge D.area))
    (hJ : J ⊆ F.goodEdges hD \ T) (hK : K ⊆ F.goodEdges hD \ T)
    (hcover : ∀ e ∈ F.goodEdges hD \ T, e ∈ J ∨ e ∈ K)
    (hoverlap : (J ∩ K).Nonempty)
    (hlocal : ∀ σ : Orientation D, F.Anchor hD σ → T ⊆ fullSelection σ →
      ∀ e f, (e ∈ J ∧ f ∈ J) ∨ (e ∈ K ∧ f ∈ K) →
        e ∈ fullSelection σ → f ∉ fullSelection σ →
        ∃ τ, Relation.ReflTransGen (Flip D) σ τ ∧ F.Anchor hD τ ∧
          fullSelection τ = insert f ((fullSelection σ).erase e))
    (θ η : Orientation D) (hθ : F.Anchor hD θ) (hη : F.Anchor hD η)
    (hTθ : T ⊆ fullSelection θ) (hTη : T ⊆ fullSelection η)
    (htotal : totalSelected θ = totalSelected η) :
    Relation.ReflTransGen (Flip D) θ η := by
  let S := {σ : Orientation D // F.Anchor hD σ ∧ T ⊆ fullSelection σ}
  let selection : S → Finset (Edge D.area) := fun σ => fullSelection σ.val \ T
  let step : S → S → Prop := fun σ τ => Relation.ReflTransGen (Flip D) σ.val τ.val
  have hinj : Function.Injective selection := by
    intro σ τ h
    apply Subtype.ext
    apply fullSelection_injective
    ext e
    by_cases he : e ∈ T
    · exact ⟨fun _ => τ.property.2 he, fun _ => σ.property.2 he⟩
    · have hm := Finset.ext_iff.mp h e
      simpa only [selection, Finset.mem_sdiff, he, not_false_eq_true, and_true] using hm
  have hsub (σ : S) : selection σ ⊆ F.goodEdges hD \ T := by
    intro e he
    obtain ⟨he, hne⟩ := Finset.mem_sdiff.mp he
    exact Finset.mem_sdiff.mpr
      ⟨((F.anchor_iff_subsets hD σ.val).mp σ.property.1).2 he, hne⟩
  have hmove (σ : S) (e f : Edge D.area)
      (hef : (e ∈ J ∧ f ∈ J) ∨ (e ∈ K ∧ f ∈ K))
      (he : e ∈ selection σ) (hf : f ∉ selection σ) :
      ∃ τ : S, Relation.ReflTransGen step σ τ ∧
        selection τ = insert f ((selection σ).erase e) := by
    have heT : e ∉ T := (Finset.mem_sdiff.mp he).2
    have hfT : f ∉ T := by
      rcases hef with h | h
      · exact (Finset.mem_sdiff.mp (hJ h.2)).2
      · exact (Finset.mem_sdiff.mp (hK h.2)).2
    have hfS : f ∉ fullSelection σ.val := fun h => hf (Finset.mem_sdiff.mpr ⟨h, hfT⟩)
    obtain ⟨τ, hp, hτ, hfull⟩ := hlocal σ.val σ.property.1 σ.property.2 e f hef
      (Finset.mem_sdiff.mp he).1 hfS
    have hTτ : T ⊆ fullSelection τ := by
      intro a ha
      rw [hfull]
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
        ⟨fun hae => heT (hae ▸ ha), σ.property.2 ha⟩)
    refine ⟨⟨τ, hτ, hTτ⟩, Relation.ReflTransGen.single hp, ?_⟩
    change fullSelection τ \ T = insert f ((fullSelection σ.val \ T).erase e)
    rw [hfull]
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    by_cases haf : a = f
    · subst a
      simp [hfT]
    · simp only [haf, false_or]
      tauto
  let source : S := ⟨θ, hθ, hTθ⟩
  let target : S := ⟨η, hη, hTη⟩
  have hcard : (selection source).card = (selection target).card := by
    have hs := Finset.card_sdiff_add_card_eq_card hTθ
    have ht := Finset.card_sdiff_add_card_eq_card hTη
    change (fullSelection θ \ T).card = (fullSelection η \ T).card
    change (fullSelection θ).card = (fullSelection η).card at htotal
    lia
  have hp := fixed_card_connectivity_in_overlapping_positions selection step
    (F.goodEdges hD \ T) J K hinj hsub hcover hoverlap hmove hcard
  have flatten {σ τ : S} (h : Relation.ReflTransGen step σ τ) :
      Relation.ReflTransGen (Flip D) σ.val τ.val := by
    induction h with
    | refl => exact .refl
    | tail _ hs ih => exact ih.trans hs
  exact flatten hp

end

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
