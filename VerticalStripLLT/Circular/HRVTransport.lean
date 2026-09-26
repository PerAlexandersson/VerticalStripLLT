import VerticalStripLLT.Circular.HRV

/-! Port of the preserved Aristotle corner-reduction candidate; see docs/ARISTOTLE.md. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ}

theorem residue_congr (D D' : Diagram n) : D.residue = D'.residue := by
  funext z
  exact Fin.ext rfl

theorem mem_normalEdges_iff (D : Diagram n) (f : Edge D.area) :
    f ∈ D.edgeData.normalEdges ↔ f ∉ D.strict := by
  simp [EdgeData.normalEdges, edgeData]

/-- Lifted steps only depend on the underlying (head, length) pairs of the selected edges. -/
theorem liftStep_eq_of {D D' : Diagram n} (A : Finset (Edge D.area))
    (A' : Finset (Edge D'.area))
    (h1 : ∀ f ∈ D.strict ∪ A, ∃ g ∈ D'.strict ∪ A', g.1 = f.1)
    (h2 : ∀ g ∈ D'.strict ∪ A', ∃ f ∈ D.strict ∪ A, f.1 = g.1) :
    D.liftStep A = D'.liftStep A' := by
  funext z w
  apply propext
  constructor
  · rintro ⟨f, hf, hz, hw⟩
    obtain ⟨g, hg, hgf⟩ := h1 f hf
    refine ⟨g, hg, ?_, ?_⟩
    · rw [residue_congr D' D, hz]
      apply Fin.ext
      simp [Edge.tail_val, Edge.head_val, Edge.length_val, hgf]
    · rw [hw]; simp [Edge.length_val, hgf]
  · rintro ⟨g, hg, hz, hw⟩
    obtain ⟨f, hf, hfg⟩ := h2 g hg
    refine ⟨f, hf, ?_, ?_⟩
    · rw [residue_congr D D', hz]
      apply Fin.ext
      simp [Edge.tail_val, Edge.head_val, Edge.length_val, hfg]
    · rw [hw]; simp [Edge.length_val, hfg]

theorem selected_eq_of {D D' : Diagram n} (A : Finset (Edge D.area))
    (A' : Finset (Edge D'.area))
    (h1 : ∀ f ∈ D.strict ∪ A, ∃ g ∈ D'.strict ∪ A', g.1 = f.1)
    (h2 : ∀ g ∈ D'.strict ∪ A', ∃ f ∈ D.strict ∪ A, f.1 = g.1) :
    D.edgeData.selected A = D'.edgeData.selected A' := by
  funext u v
  apply propext
  constructor
  · rintro ⟨f, hf, hu, hv⟩
    obtain ⟨g, hg, hgf⟩ := h1 f hf
    refine ⟨g, hg, ?_, ?_⟩
    · rw [← hu]
      change g.tail = f.tail
      apply Fin.ext
      simp [Edge.tail_val, Edge.head_val, Edge.length_val, hgf]
    · rw [← hv]
      change g.head = f.head
      apply Fin.ext
      simp [Edge.head_val, hgf]
  · rintro ⟨g, hg, hu, hv⟩
    obtain ⟨f, hf, hfg⟩ := h2 g hg
    refine ⟨f, hf, ?_, ?_⟩
    · rw [← hu]
      change f.tail = g.tail
      apply Fin.ext
      simp [Edge.tail_val, Edge.head_val, Edge.length_val, hfg]
    · rw [← hv]
      change f.head = g.head
      apply Fin.ext
      simp [Edge.head_val, hfg]

end Diagram

namespace Orientation

variable {n : ℕ}

theorem hrv_eq_of_liftStep {D D' : Diagram n} (θ : Orientation D) (θ' : Orientation D')
    (h : D.liftStep θ.val = D'.liftStep θ'.val) : θ.hrv = θ'.hrv := by
  funext u
  simp only [hrv, liftedHRV]
  rw [h]
  rfl

theorem hrvMonomial_eq_of_hrv {D D' : Diagram n} (θ : Orientation D) (θ' : Orientation D')
    (h : θ.hrv = θ'.hrv) : θ.hrvMonomial = θ'.hrvMonomial := by
  unfold hrvMonomial
  simp only [h]

end Orientation

end VerticalStripLLT.Circular
