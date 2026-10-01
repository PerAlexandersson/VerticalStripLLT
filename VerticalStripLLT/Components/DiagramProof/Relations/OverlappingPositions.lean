import VerticalStripLLT.Components.DiagramProof.Relations.FiniteSubsetPaths

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

/-- The same exchange argument on a specified pool of allowed positions. -/
theorem fixed_card_connectivity_in_overlapping_positions
    (selection : State → Finset V) (step : State → State → Prop)
    (P J K : Finset V) (hinj : Function.Injective selection)
    (hselection : ∀ σ, selection σ ⊆ P)
    (hcover : ∀ a ∈ P, a ∈ J ∨ a ∈ K) (hoverlap : (J ∩ K).Nonempty)
    (hlocal : ∀ σ a b, (a ∈ J ∧ b ∈ J) ∨ (a ∈ K ∧ b ∈ K) →
      a ∈ selection σ → b ∉ selection σ →
      ∃ τ, Relation.ReflTransGen step σ τ ∧
        selection τ = insert b ((selection σ).erase a))
    {σ τ : State} (hcard : (selection σ).card = (selection τ).card) :
    Relation.ReflTransGen step σ τ := by
  classical
  let R : V → V → Prop := fun a b => (a ∈ J ∧ b ∈ J) ∨ (a ∈ K ∧ b ∈ K)
  let label : V → Bool := fun a => decide (a ∈ P)
  have hlabel (ξ : State) (a : V) (ha : a ∈ selection ξ) : label a = true :=
    decide_eq_true (hselection ξ ha)
  have hpaths (a b : V) (ha : a ∈ P) (hb : b ∈ P) :
      Relation.ReflTransGen R a b := by
    obtain ⟨c, hc⟩ := hoverlap
    obtain ⟨hcJ, hcK⟩ := Finset.mem_inter.mp hc
    have hac : R a c := (hcover a ha).elim (fun h => Or.inl ⟨h, hcJ⟩)
      (fun h => Or.inr ⟨h, hcK⟩)
    have hcb : R c b := (hcover b hb).elim (fun h => Or.inl ⟨hcJ, h⟩)
      (fun h => Or.inr ⟨hcK, h⟩)
    exact (Relation.ReflTransGen.single hac).tail hcb
  apply fixed_label_connectivity selection step label hinj
  · intro ξ a b hab ha hb
    have hbP : b ∈ P := of_decide_eq_true (hab.symm.trans (hlabel ξ a ha))
    exact reflTransGen_exchange selection step R hlocal
      (hpaths a b (hselection ξ ha) hbP) ha hb
  · intro l
    cases l with
    | false =>
      have hz (ξ : State) : (selection ξ).filter (fun a => label a = false) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro a ha hfalse
        have := hlabel ξ a ha
        simp_all
      rw [hz, hz]
    | true =>
      have ht (ξ : State) : (selection ξ).filter (fun a => label a = true) = selection ξ :=
        Finset.filter_eq_self.mpr (hlabel ξ)
      rw [ht, ht]
      exact hcard

end VerticalStripLLT.Circular.DiagramProof
