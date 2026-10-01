import VerticalStripLLT.Components.DiagramProof.Preparation.ParallelMoves
import VerticalStripLLT.Components.DiagramProof.Relations.FiniteSubsetPaths

/-! Parallel-copy rearrangements lifted to actual flip paths, with exact exterior. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- Ordered chain terminals; an anchor uses only diagonal corners and increasing pairs. -/
noncomputable def copyLabel (e : Edge D.area) : Fin n × Fin n :=
  (F.terminal hforward e.tail, F.terminal hforward e.head)

/-- Number of selected copies in each ordered terminal pair, including fixed corners. -/
noncomputable def occupancy (θ : Orientation D) (p : Fin n × Fin n) : ℕ := by
  classical
  exact ((fullSelection θ).filter (fun e => F.copyLabel hforward e = p)).card

private theorem flatten_anchor_path
    {θ η : {θ : Orientation D // F.Anchor hforward θ}}
    (hp : Relation.ReflTransGen
      (fun α β : {θ : Orientation D // F.Anchor hforward θ} =>
        Relation.ReflTransGen (Flip D) α.val β.val) θ η) :
    Relation.ReflTransGen (Flip D) θ.val η.val := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.trans hs

/-- Any occupied good copy can be moved to any vacant copy of the same ordered pair. -/
theorem exists_parallelCopyExchange (θ : Orientation D) (hθ : F.Anchor hforward θ)
    (e f : Edge D.area)
    (hegood : F.terminal hforward e.tail < F.terminal hforward e.head)
    (ht : F.terminal hforward e.tail = F.terminal hforward f.tail)
    (hh : F.terminal hforward e.head = F.terminal hforward f.head)
    (he : e ∈ fullSelection θ) (hf : f ∉ fullSelection θ) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hforward η ∧
      fullSelection η = insert f ((fullSelection θ).erase e) := by
  classical
  let S := {θ : Orientation D // F.Anchor hforward θ}
  let selection : S → Finset (Edge D.area) := fun σ => fullSelection σ.val
  let step : S → S → Prop := fun σ τ => Relation.ReflTransGen (Flip D) σ.val τ.val
  have hlocal : ∀ σ a b, Relation.SymmGen F.CopyLink a b →
      a ∈ selection σ → b ∉ selection σ →
      ∃ τ, Relation.ReflTransGen step σ τ ∧
        selection τ = insert b ((selection σ).erase a) := by
    intro σ a b hab ha hb
    obtain ⟨τ, hp, hτ, hfull⟩ :=
      F.exists_adjacentCopyExchange hforward σ.val σ.property a b hab ha hb
    exact ⟨⟨τ, hτ⟩, Relation.ReflTransGen.single hp, hfull⟩
  have hpath := F.copy_reachable_undirected hforward e f hegood ht hh
  obtain ⟨η, hp, hfull⟩ := reflTransGen_exchange selection step
    (Relation.SymmGen F.CopyLink) hlocal (σ := ⟨θ, hθ⟩) hpath he hf
  exact ⟨η.val, F.flatten_anchor_path hforward hp, η.property, hfull⟩

/-- Anchors with identical occupancy vectors belong to the same actual flip component. -/
theorem anchors_connected_of_occupancy {θ η : Orientation D}
    (hθ : F.Anchor hforward θ) (hη : F.Anchor hforward η)
    (hcounts : ∀ p, F.occupancy hforward θ p = F.occupancy hforward η p) :
    Relation.ReflTransGen (Flip D) θ η := by
  classical
  let S := {θ : Orientation D // F.Anchor hforward θ}
  let selection : S → Finset (Edge D.area) := fun σ => fullSelection σ.val
  let step : S → S → Prop := fun σ τ => Relation.ReflTransGen (Flip D) σ.val τ.val
  have hinj : Function.Injective selection := by
    intro σ τ h
    exact Subtype.ext (fullSelection_injective h)
  have hlocal : ∀ σ a b, F.copyLabel hforward a = F.copyLabel hforward b →
      a ∈ selection σ → b ∉ selection σ →
      ∃ τ, Relation.ReflTransGen step σ τ ∧
        selection τ = insert b ((selection σ).erase a) := by
    intro σ a b hab ha hb
    have ht := congrArg Prod.fst hab
    have hh := congrArg Prod.snd hab
    change F.terminal hforward a.tail = F.terminal hforward b.tail at ht
    change F.terminal hforward a.head = F.terminal hforward b.head at hh
    have han : a ∉ F.edges := by
      intro haC
      have hbC := (F.terminal_eq_iff_mem hforward b).mp
        (ht.symm.trans (((F.terminal_eq_iff_mem hforward a).mpr haC).trans hh))
      exact hb (σ.property.1 hbC)
    have hagood := (σ.property.2 a ha).resolve_left han
    obtain ⟨τ, hp, hτ, hfull⟩ :=
      F.exists_parallelCopyExchange hforward σ.val σ.property a b hagood ht hh ha hb
    exact ⟨⟨τ, hτ⟩, Relation.ReflTransGen.single hp, hfull⟩
  have hp := fixed_label_connectivity selection step (F.copyLabel hforward) hinj hlocal
    (σ := ⟨θ, hθ⟩) (τ := ⟨η, hη⟩) hcounts
  exact F.flatten_anchor_path hforward hp

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
