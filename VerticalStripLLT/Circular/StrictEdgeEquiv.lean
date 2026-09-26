import VerticalStripLLT.Circular.NeutralTransport
import VerticalStripLLT.Circular.EdgeLength

/-! Transport of strict edges along an isomorphism of selected graphs. -/

namespace VerticalStripLLT.Circular

namespace Diagram

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {D D' : Diagram n}

private theorem edge_eq_of_endpoints {A : CircularArea n} {e f : Edge A}
    (ht : e.tail = f.tail) (hh : e.head = f.head) : e = f := by
  apply Subtype.ext
  apply Prod.ext
  · exact hh
  · apply Fin.ext
    exact Edge.length_eq_of_endpoints ht hh

private theorem strict_target_exists (σ : Fin n ≃ Fin n)
    (hσ : ∀ u v, D.edgeData.selected ∅ u v ↔
      D'.edgeData.selected ∅ (σ u) (σ v)) (e : D.StrictEdge) :
    ∃ f : D'.StrictEdge,
      f.val.tail = σ e.val.tail ∧ f.val.head = σ e.val.head := by
  have hs : D.edgeData.selected ∅ e.val.tail e.val.head := by
    exact ⟨e.val, by simp [Diagram.edgeData, e.property], rfl, rfl⟩
  rcases (hσ e.val.tail e.val.head).mp hs with ⟨f, hf, ht, hh⟩
  have hf' : f ∈ D'.strict := by
    simpa [Diagram.edgeData] using hf
  exact ⟨⟨f, hf'⟩, ht, hh⟩

noncomputable def strictEdgeMap (σ : Fin n ≃ Fin n)
    (hσ : ∀ u v, D.edgeData.selected ∅ u v ↔
      D'.edgeData.selected ∅ (σ u) (σ v)) :
    D.StrictEdge → D'.StrictEdge := fun e =>
  Classical.choose (strict_target_exists σ hσ e)

private theorem strictEdgeMap_spec (σ : Fin n ≃ Fin n)
    (hσ : ∀ u v, D.edgeData.selected ∅ u v ↔
      D'.edgeData.selected ∅ (σ u) (σ v)) (e : D.StrictEdge) :
    (strictEdgeMap σ hσ e).val.tail = σ e.val.tail ∧
      (strictEdgeMap σ hσ e).val.head = σ e.val.head := by
  exact Classical.choose_spec (strict_target_exists σ hσ e)

noncomputable def strictEdgeEquiv (σ : Fin n ≃ Fin n)
    (hσ : ∀ u v, D.edgeData.selected ∅ u v ↔
      D'.edgeData.selected ∅ (σ u) (σ v)) :
    D.StrictEdge ≃ D'.StrictEdge := by
  apply Equiv.ofBijective (strictEdgeMap σ hσ)
  constructor
  · intro e f hef
    have he := strictEdgeMap_spec σ hσ e
    have hf := strictEdgeMap_spec σ hσ f
    apply Subtype.ext
    apply edge_eq_of_endpoints
    · apply σ.injective
      rw [← he.1, hef, hf.1]
    · apply σ.injective
      rw [← he.2, hef, hf.2]
  · intro f
    have hs : D'.edgeData.selected ∅ f.val.tail f.val.head := by
      exact ⟨f.val, by simp [Diagram.edgeData, f.property], rfl, rfl⟩
    rcases (hσ (σ.symm f.val.tail) (σ.symm f.val.head)).mpr (by
      simpa using hs) with ⟨e, he, ht, hh⟩
    have he' : e ∈ D.strict := by
      simpa [Diagram.edgeData] using he
    change e.tail = σ.symm f.val.tail at ht
    change e.head = σ.symm f.val.head at hh
    let e' : D.StrictEdge := ⟨e, he'⟩
    have hm := strictEdgeMap_spec σ hσ e'
    have htail : (strictEdgeMap σ hσ e').val.tail = f.val.tail := by
      calc
        (strictEdgeMap σ hσ e').val.tail = σ e'.val.tail := hm.1
        _ = f.val.tail := by dsimp [e']; rw [ht]; simp
    have hhead : (strictEdgeMap σ hσ e').val.head = f.val.head := by
      calc
        (strictEdgeMap σ hσ e').val.head = σ e'.val.head := hm.2
        _ = f.val.head := by dsimp [e']; rw [hh]; simp
    refine ⟨e', ?_⟩
    apply Subtype.ext
    exact edge_eq_of_endpoints htail hhead

theorem strictEdgeEquiv_tail (σ : Fin n ≃ Fin n)
    (hσ : ∀ u v, D.edgeData.selected ∅ u v ↔
      D'.edgeData.selected ∅ (σ u) (σ v)) (e : D.StrictEdge) :
    (strictEdgeEquiv σ hσ e).val.tail = σ e.val.tail := by
  exact strictEdgeMap_spec σ hσ e |>.1

theorem strictEdgeEquiv_head (σ : Fin n ≃ Fin n)
    (hσ : ∀ u v, D.edgeData.selected ∅ u v ↔
      D'.edgeData.selected ∅ (σ u) (σ v)) (e : D.StrictEdge) :
    (strictEdgeEquiv σ hσ e).val.head = σ e.val.head := by
  exact strictEdgeMap_spec σ hσ e |>.2

end Diagram
end VerticalStripLLT.Circular
