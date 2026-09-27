import VerticalStripLLT.Circular.PairColoringBridge

/-! Selected relations under exchange of a normal edge, before orientation construction. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

/-- Inserting an edge adds exactly its directed endpoint pair. -/
theorem selected_insert_iff (A : Finset (Edge D.area)) (e : Edge D.area)
    (u v : Fin n) :
    D.edgeData.selected (insert e A) u v ↔
      (e.tail = u ∧ e.head = v) ∨ D.edgeData.selected A u v := by
  constructor
  · rintro ⟨f, hf, hu, hv⟩
    rcases Finset.mem_union.mp hf with hs | ha
    · exact Or.inr ⟨f, Finset.mem_union.mpr (Or.inl hs), hu, hv⟩
    · rcases Finset.mem_insert.mp ha with rfl | ha
      · exact Or.inl ⟨hu, hv⟩
      · exact Or.inr ⟨f, Finset.mem_union.mpr (Or.inr ha), hu, hv⟩
  · rintro (⟨hu, hv⟩ | ⟨f, hf, hu, hv⟩)
    · exact ⟨e, Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _)), hu, hv⟩
    · refine ⟨f, ?_, hu, hv⟩
      rcases Finset.mem_union.mp hf with hs | ha
      · exact Finset.mem_union.mpr (Or.inl hs)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_of_mem ha))

/-- Erasing a normal edge removes exactly its directed endpoint pair. -/
theorem selected_erase_normal_iff (A : Finset (Edge D.area)) (e : Edge D.area)
    (he : e ∈ D.edgeData.normalEdges) (u v : Fin n) :
    D.edgeData.selected (A.erase e) u v ↔
      D.edgeData.selected A u v ∧ ¬ (e.tail = u ∧ e.head = v) := by
  have hns : e ∉ D.strict := (Finset.mem_sdiff.mp he).2
  constructor
  · rintro ⟨f, hf, hu, hv⟩
    refine ⟨⟨f, ?_, hu, hv⟩, ?_⟩
    · rcases Finset.mem_union.mp hf with hs | ha
      · exact Finset.mem_union.mpr (Or.inl hs)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_erase.mp ha).2)
    · intro heuv
      have hfe : f = e := by
        apply D.endpointEmbedding.injective
        change (f.tail, f.head) = (e.tail, e.head)
        exact Prod.ext (hu.trans heuv.1.symm) (hv.trans heuv.2.symm)
      subst f
      rcases Finset.mem_union.mp hf with hs | ha
      · exact hns hs
      · exact (Finset.mem_erase.mp ha).1 rfl
  · rintro ⟨⟨f, hf, hu, hv⟩, hnot⟩
    refine ⟨f, ?_, hu, hv⟩
    rcases Finset.mem_union.mp hf with hs | ha
    · exact Finset.mem_union.mpr (Or.inl hs)
    · apply Finset.mem_union.mpr
      apply Or.inr
      apply Finset.mem_erase.mpr
      refine ⟨?_, ha⟩
      intro hfe
      subst f
      exact hnot ⟨hu, hv⟩

/-- Exchanging a normal edge has an exact relation formula for arbitrary edge sets. -/
theorem selected_insert_erase_normal_iff (A : Finset (Edge D.area))
    (e f : Edge D.area) (he : e ∈ D.edgeData.normalEdges) (u v : Fin n) :
    D.edgeData.selected (insert f (A.erase e)) u v ↔
      (f.tail = u ∧ f.head = v) ∨
        (D.edgeData.selected A u v ∧ ¬ (e.tail = u ∧ e.head = v)) := by
  rw [D.selected_insert_iff, D.selected_erase_normal_iff A e he]

/-- The endpoint form used to exchange the two short edges of a triple. -/
theorem selected_short_swap_iff (A : Finset (Edge D.area))
    (eab ebc : Edge D.area) (heab : eab ∈ D.edgeData.normalEdges)
    {a b c : Fin n} (hab : (eab.tail, eab.head) = (a, b))
    (hbc : (ebc.tail, ebc.head) = (b, c)) (u v : Fin n) :
    D.edgeData.selected (insert ebc (A.erase eab)) u v ↔
      (u = b ∧ v = c) ∨
        (D.edgeData.selected A u v ∧ ¬ (u = a ∧ v = b)) := by
  obtain ⟨habt, habh⟩ := Prod.mk.inj hab
  obtain ⟨hbct, hbch⟩ := Prod.mk.inj hbc
  rw [D.selected_insert_erase_normal_iff A eab ebc heab]
  simp only [habt, habh, hbct, hbch, eq_comm]

end VerticalStripLLT.Circular.Diagram

namespace VerticalStripLLT.Components

/-- Reversing an exchange recovers the original set when precisely the old edge was present. -/
theorem insert_erase_exchange_inverse {E : Type*} [DecidableEq E]
    (A : Finset E) {e f : E} (he : e ∈ A) (hf : f ∉ A) :
    insert e ((insert f (A.erase e)).erase f) = A := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_erase]
  grind

end VerticalStripLLT.Components
