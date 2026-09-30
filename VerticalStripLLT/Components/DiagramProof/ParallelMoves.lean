import VerticalStripLLT.Components.DiagramProof.CopyPaths
import VerticalStripLLT.Components.DiagramProof.CrossingSlide
import VerticalStripLLT.Circular.ComponentSemantics

/-! Neighboring parallel-copy exchanges are actual paths with exact restored exterior. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

/-- Translate the endpoint relation of an exchange into equality of full selected edge sets. -/
theorem fullSelection_eq_of_exchange {θ η : Orientation D} (e f : Edge D.area)
    (h : ∀ u v, D.edgeData.selected η.val u v ↔
      exchangeRelation (D.edgeData.selected θ.val) e.tail e.head f.tail f.head u v) :
    fullSelection η = insert f ((fullSelection θ).erase e) := by
  classical
  ext g
  have endpoints (k : Edge D.area) : (g.tail = k.tail ∧ g.head = k.head) ↔ g = k := by
    refine ⟨fun hk => D.endpointEmbedding.injective (Prod.ext hk.1 hk.2), ?_⟩
    intro hk
    subst k
    exact ⟨rfl, rfl⟩
  rw [mem_fullSelection_iff_selected, h]
  simp only [exchangeRelation, endpoints, ← mem_fullSelection_iff_selected,
    Finset.mem_insert, Finset.mem_erase]
  tauto

namespace CornerFamily

variable (F : CornerFamily D) (hforward : Forward D)

/-- Replacing a non-corner by another good edge always defines an actual anchor. -/
theorem exists_anchor_exchange (θ : Orientation D) (hθ : F.Anchor hforward θ)
    (e f : Edge D.area) (he : e ∉ F.edges) (hf : F.GoodEdge hforward f) :
    ∃ η : Orientation D, F.Anchor hforward η ∧
      fullSelection η = insert f ((fullSelection θ).erase e) := by
  classical
  let A := insert f ((fullSelection θ).erase e)
  have hC : F.edges ⊆ A := by
    intro g hg
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
      ⟨fun h => he (h ▸ hg), hθ.1 hg⟩)
  have hA : A ⊆ F.goodEdges hforward := by
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact (F.mem_goodEdges hforward _).mpr hf
    · exact (F.mem_goodEdges hforward g).mpr (hθ.2 g (Finset.mem_erase.mp hg).2)
  exact ⟨ofFullSelection hforward A (F.contains_strict.trans hC),
    F.anchor_ofFullSelection hforward A hC hA, fullSelection_ofFullSelection hforward A _⟩

/-- Slide a selected copy to the next vacant good position, retaining the full exterior. -/
theorem exists_forwardCopyExchange (θ : Orientation D) (hθ : F.Anchor hforward θ)
    (e f : Edge D.area) (hlink : F.CopyLink e f)
    (hegood : F.terminal hforward e.tail < F.terminal hforward e.head)
    (he : e ∈ fullSelection θ) (hf : f ∉ fullSelection θ) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hforward η ∧
      fullSelection η = insert f ((fullSelection θ).erase e) := by
  have covers {u v : Fin n} (hstep : F.step u v) : Cover θ u v := by
    obtain ⟨g, hg, hgt, hgh⟩ := (F.step_iff u v).mp hstep
    have hc := F.commonCover_of_anchor hforward hθ g hg
    simpa only [hgt, hgh] using hc
  obtain ⟨η, hp, _, _, hrel⟩ := exists_crossingSlide hforward θ e.tail e.head f.tail f.head
    (hforward e) hlink.2.2 (hforward f) (covers hlink.1) (covers hlink.2.1)
    ((mem_fullSelection_iff_selected θ e).mp he)
    (fun h => hf ((mem_fullSelection_iff_selected θ f).mpr h))
  have hfull := fullSelection_eq_of_exchange e f hrel
  have hen : e ∉ F.edges := fun h => hegood.ne ((F.terminal_eq_iff_mem hforward e).mpr h)
  have hfgood : F.GoodEdge hforward f := Or.inr (by
    rw [← F.terminal_eq_of_step hforward hlink.1,
      ← F.terminal_eq_of_step hforward hlink.2.1]
    exact hegood)
  obtain ⟨ξ, hξ, hfullξ⟩ := F.exists_anchor_exchange hforward θ hθ e f hen hfgood
  have hηξ : η = ξ := fullSelection_injective (hfull.trans hfullξ.symm)
  exact ⟨η, hp, hηξ ▸ hξ, hfull⟩

/-- The reverse slide has the same endpoint guarantee. -/
theorem exists_backwardCopyExchange (θ : Orientation D) (hθ : F.Anchor hforward θ)
    (e f : Edge D.area) (hlink : F.CopyLink f e)
    (hegood : F.terminal hforward e.tail < F.terminal hforward e.head)
    (he : e ∈ fullSelection θ) (hf : f ∉ fullSelection θ) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hforward η ∧
      fullSelection η = insert f ((fullSelection θ).erase e) := by
  classical
  have hfgood : F.terminal hforward f.tail < F.terminal hforward f.head := by
    rw [F.terminal_eq_of_step hforward hlink.1,
      F.terminal_eq_of_step hforward hlink.2.1]
    exact hegood
  have hen : e ∉ F.edges := fun h => hegood.ne ((F.terminal_eq_iff_mem hforward e).mpr h)
  obtain ⟨η, hη, hfull⟩ := F.exists_anchor_exchange hforward θ hθ e f hen (Or.inr hfgood)
  have hne : e ≠ f := fun h => hf (h ▸ he)
  have hηf : f ∈ fullSelection η := by rw [hfull]; exact Finset.mem_insert_self _ _
  have hηe : e ∉ fullSelection η := by simp only [hfull, Finset.mem_insert, Finset.mem_erase]; grind
  obtain ⟨ξ, hp, _, hξ⟩ := F.exists_forwardCopyExchange hforward η hη f e hlink hfgood hηf hηe
  have hξθ : ξ = θ := by
    apply fullSelection_injective
    rw [hξ, hfull]
    ext g
    simp only [Finset.mem_insert, Finset.mem_erase]
    grind
  subst ξ
  exact ⟨η, flip_reachable_symm hp, hη, hfull⟩

/-- The state interface for either direction of a neighboring occupied/vacant exchange. -/
theorem exists_adjacentCopyExchange (θ : Orientation D) (hθ : F.Anchor hforward θ)
    (e f : Edge D.area) (hlink : Relation.SymmGen F.CopyLink e f)
    (he : e ∈ fullSelection θ) (hf : f ∉ fullSelection θ) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hforward η ∧
      fullSelection η = insert f ((fullSelection θ).erase e) := by
  have hen : e ∉ F.edges := by
    rcases hlink with hlink | hlink
    · exact (F.copyLink_not_mem hlink).1
    · exact (F.copyLink_not_mem hlink).2
  have hegood := (hθ.2 e he).resolve_left hen
  rcases hlink with hlink | hlink
  · exact F.exists_forwardCopyExchange hforward θ hθ e f hlink hegood he hf
  · exact F.exists_backwardCopyExchange hforward θ hθ e f hlink hegood he hf

end CornerFamily

end VerticalStripLLT.Circular.DiagramProof
