import VerticalStripLLT.Components.DiagramProof.SelectedRelation
import VerticalStripLLT.Components.DiagramProof.InducedCorners

/-!
# Natural, strict and selected endpoint relations

A forward diagram is determined, for the purposes of the diagram proof, by its
natural and strict endpoint relations, and an actual state by its selected
relation. These are the low-level relational facts used throughout.
-/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- The strict endpoint relation of a diagram. -/
def strictRel (D : Diagram n) (u v : Fin n) : Prop :=
  ∃ e ∈ D.strict, e.tail = u ∧ e.head = v

theorem naturalRel_of_strictRel {u v : Fin n} (h : strictRel D u v) :
    naturalRel D u v := by
  obtain ⟨e, -, ht, hh⟩ := h
  exact ⟨e, ht, hh⟩

theorem naturalRel_of_selected {θ : Orientation D} {u v : Fin n}
    (h : D.edgeData.selected θ.val u v) : naturalRel D u v := by
  obtain ⟨e, -, ht, hh⟩ := h
  exact ⟨e, ht, hh⟩

theorem selected_of_strictRel (θ : Orientation D) {u v : Fin n} (h : strictRel D u v) :
    D.edgeData.selected θ.val u v := by
  obtain ⟨e, he, ht, hh⟩ := h
  exact ⟨e, Finset.mem_union_left _ he, ht, hh⟩

theorem naturalRel_interval (hD : Forward D) {a b c : Fin n}
    (h : naturalRel D a c) (hab : a < b) (hbc : b < c) :
    naturalRel D a b ∧ naturalRel D b c := by
  obtain ⟨e, rfl, rfl⟩ := h
  have he := D.naturalLift_of_tail_lt_head e (hD e)
  exact ⟨exists_edge_of_naturalLift_of_le he le_rfl hab hbc.le,
    exists_edge_of_naturalLift_of_le he hab.le hbc le_rfl⟩

/-- A strict pair is a maximal natural interval. -/
theorem strictRel_maximal (hD : Forward D) {s t x y : Fin n} (hst : strictRel D s t)
    (hxy : naturalRel D x y) (hxs : x ≤ s) (hty : t ≤ y) : x = s ∧ y = t := by
  obtain ⟨e, he, rfl, rfl⟩ := hst
  obtain ⟨f, rfl, rfl⟩ := hxy
  have hfe := (isCorner_iff_maximal hD e).mp (D.strict_corner e he) f hxs hty
  subst hfe
  exact ⟨rfl, rfl⟩

/-- A pair properly inside a natural pair is not strict. -/
theorem not_strictRel_of_lt (hD : Forward D) {x y s t : Fin n} (hxy : naturalRel D x y)
    (hxs : x ≤ s) (hty : t ≤ y) (hne : x < s ∨ t < y) : ¬ strictRel D s t := by
  intro hst
  obtain ⟨h1, h2⟩ := strictRel_maximal hD hst hxy hxs hty
  rcases hne with h | h
  · exact h.ne h1
  · exact h.ne h2.symm

/-- The total selected size counts the selected endpoint pairs. -/
theorem totalSelected_eq_card_selected {D : Diagram n} (θ : Orientation D) :
    totalSelected θ = (Finset.univ.filter fun p : Fin n × Fin n =>
      D.edgeData.selected θ.val p.1 p.2).card := by
  rw [totalSelected, ← Finset.card_map D.endpointEmbedding]
  congr 1
  ext p
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact (mem_fullSelection_iff_selected θ e).mp he
  · rintro ⟨e, he, ht, hh⟩
    exact ⟨e, he, Prod.ext ht hh⟩

/-- Orientations with the same selected endpoint relation are equal. -/
theorem orientation_eq_of_selected_iff {θ η : Orientation D}
    (h : ∀ u v, D.edgeData.selected θ.val u v ↔ D.edgeData.selected η.val u v) :
    θ = η := by
  apply fullSelection_injective
  ext e
  rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected]
  exact h e.tail e.head

/-- A forward relation between natural and strict pairs is an actual state. -/
theorem exists_orientation_of_relation (hD : Forward D) (R : Fin n → Fin n → Prop)
    (hnat : ∀ u v, R u v → naturalRel D u v) (hstrict : ∀ u v, strictRel D u v → R u v) :
    ∃ θ : Orientation D, ∀ u v, D.edgeData.selected θ.val u v ↔ R u v :=
  ⟨ofSelectedRelation hD R hnat (fun e he => hstrict _ _ ⟨e, he, rfl, rfl⟩),
    selected_ofSelectedRelation hD R hnat _⟩

end

end VerticalStripLLT.Circular.DiagramProof
