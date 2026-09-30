import VerticalStripLLT.Components.DiagramProof.FiniteSubsetPaths

/-! Fixed-size rearrangement from local exchanges on connected position sets. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V State : Type*} [DecidableEq V]

/-- Connected position paths and exact neighboring exchanges suffice at each fixed size. -/
theorem fixed_card_connectivity_of_position_paths
    (selection : State → Finset V) (step : State → State → Prop)
    (R : V → V → Prop) (hinj : Function.Injective selection)
    (hpaths : ∀ a b, Relation.ReflTransGen R a b)
    (hlocal : ∀ σ a b, R a b → a ∈ selection σ → b ∉ selection σ →
      ∃ τ, Relation.ReflTransGen step σ τ ∧
        selection τ = insert b ((selection σ).erase a))
    {σ τ : State} (hcard : (selection σ).card = (selection τ).card) :
    Relation.ReflTransGen step σ τ := by
  apply fixed_label_connectivity selection step (fun _ => ()) hinj
  · intro ξ a b _ ha hb
    exact reflTransGen_exchange selection step R hlocal (hpaths a b) ha hb
  · intro l
    cases l
    simpa using hcard

/-- Exchanges supported in either of two overlapping sets connect every fixed-size layer.
Use the subtype of allowed positions when the ambient position type is larger. -/
theorem fixed_card_connectivity_of_overlapping_positions
    (selection : State → Finset V) (step : State → State → Prop)
    (J K : Finset V) (hinj : Function.Injective selection)
    (hcover : ∀ a, a ∈ J ∨ a ∈ K) (hoverlap : (J ∩ K).Nonempty)
    (hlocal : ∀ σ a b, (a ∈ J ∧ b ∈ J) ∨ (a ∈ K ∧ b ∈ K) →
      a ∈ selection σ → b ∉ selection σ →
      ∃ τ, Relation.ReflTransGen step σ τ ∧
        selection τ = insert b ((selection σ).erase a))
    {σ τ : State} (hcard : (selection σ).card = (selection τ).card) :
    Relation.ReflTransGen step σ τ := by
  let R : V → V → Prop := fun a b => (a ∈ J ∧ b ∈ J) ∨ (a ∈ K ∧ b ∈ K)
  apply fixed_card_connectivity_of_position_paths selection step R hinj ?_ hlocal hcard
  obtain ⟨c, hc⟩ := hoverlap
  obtain ⟨hcJ, hcK⟩ := Finset.mem_inter.mp hc
  intro a b
  have hac : R a c := (hcover a).elim (fun h => Or.inl ⟨h, hcJ⟩)
    (fun h => Or.inr ⟨h, hcK⟩)
  have hcb : R c b := (hcover b).elim (fun h => Or.inl ⟨hcJ, h⟩)
    (fun h => Or.inr ⟨hcK, h⟩)
  exact (Relation.ReflTransGen.single hac).tail hcb

end VerticalStripLLT.Circular.DiagramProof
