import VerticalStripLLT.Circular.DDResolvedRows
import VerticalStripLLT.Circular.DDResolvedStrict
import VerticalStripLLT.Circular.DNTargetPairs

/-! Local boundary, gap and acyclicity transport for the resolved DD successor. -/

namespace VerticalStripLLT.Circular.Diagram

variable {n : ℕ} {D : Diagram n}

theorem unstrict_selected {g : Edge D.area} (hg : g ∈ D.strict) {u v : Fin n}
    (h : (D.unstrict g hg).edgeData.selected ∅ u v) :
    D.edgeData.selected ∅ u v ∧ v ≠ g.head := by
  obtain ⟨a, ha, hu, hv⟩ := h
  have ha' : a ∈ D.strict.erase g :=
    (Finset.mem_union.mp ha).resolve_right (Finset.notMem_empty _)
  obtain ⟨hag, has⟩ := Finset.mem_erase.mp ha'
  refine ⟨⟨a, Finset.mem_union_left _ has, hu, hv⟩, ?_⟩
  intro hvg
  exact hag (D.strict_edge_eq_of_head_eq has hg (hv.trans hvg))

theorem selected_of_mem_strict {a : Edge D.area} (ha : a ∈ D.strict) :
    D.edgeData.selected ∅ a.tail a.head :=
  ⟨a, Finset.mem_union_left _ ha, rfl, rfl⟩

namespace DDLocalData

variable {t : ℤ} (B : D.DDLocalData t)

theorem resolved_boundary_ge (z : ℤ) (hz : D.residue z ≠ D.residue (D.boundary t + 1)) :
    D.boundary z ≤ B.resolved.boundary z := by
  rw [boundary, boundary, B.resolved_residue, B.resolved_area]
  by_cases h : D.residue z = D.residue t
  · rw [h, Function.update_self]
    lia
  · rw [Function.update_of_ne h, Function.update_of_ne hz]

theorem resolved_eastGap_of_ne (z : ℤ)
    (h₀ : D.residue z ≠ D.residue (D.boundary t + 1)) (h₁ : D.residue z ≠ D.residue t)
    (h₂ : D.residue (z + 1) ≠ D.residue (D.boundary t + 1))
    (h₃ : D.residue (z + 1) ≠ D.residue t)
    (h₄ : D.residue z ≠ D.residue (D.boundary t)) :
    B.resolved.eastGap z = D.eastGap z := by
  unfold eastGap
  rw [B.resolved_boundary_of_ne z h₀ h₁, B.resolved_boundary_of_ne (z + 1) h₂ h₃]
  by_cases hs : D.strictAt z
  · rw [ite_eq_left hs, ite_eq_left ((B.resolved_strictAt_iff z).mpr ⟨hs, h₄⟩)]
  · rw [ite_eq_right hs, ite_eq_right (fun h => hs ((B.resolved_strictAt_iff z).mp h).1)]

/-- Swapping the contact row and its successor conjugates the resolved strict relation
into the source strict relation. -/
theorem resolved_selected_swap (ht : D.EligibleDE t) {u v : Fin n}
    (h : B.resolved.edgeData.selected ∅ u v) :
    D.edgeData.selected ∅ (Equiv.swap B.e.head (D.area.next B.e.head) u)
      (Equiv.swap B.e.head (D.area.next B.e.head) v) := by
  have hq : D.area.next B.e.head = D.residue (D.boundary t + 1) := B.head.symm.trans B.gh
  have hfree : ∀ w, ¬ D.edgeData.selected ∅ (D.area.next B.e.head) w := by
    rw [hq]; exact ht.parallel_end_free D
  have hselE := selected_of_mem_strict B.he
  have hselF := selected_of_mem_strict B.hf
  have hetp : B.e.tail ≠ B.e.head := B.e.tail_ne_head
  have hetq : B.e.tail ≠ D.area.next B.e.head := fun h => hfree _ (h ▸ hselE)
  have hfhp : B.f.head ≠ B.e.head := fun h => B.f.tail_ne_head (B.contact.trans h.symm)
  have hfhq : B.f.head ≠ D.area.next B.e.head := fun h =>
    B.hfg (D.strict_edge_eq_of_head_eq B.hf B.hg (h.trans B.head.symm))
  unfold resolved ddResolved at h
  rcases (Diagram.dnSuccessor_selected_iff _ _ _ _ _ _ _ _ _ _ _ u v).mp h with
    ⟨hs, hne, hnf⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
  · obtain ⟨hs, hvg⟩ := unstrict_selected B.hg hs
    have huq : u ≠ D.area.next B.e.head := fun h => hfree v (h ▸ hs)
    have hup : u ≠ B.e.head := by
      intro hup
      apply hnf
      refine ⟨hup.trans B.contact.symm, ?_⟩
      have hselF' : D.edgeData.selected ∅ u B.f.head := by
        rw [hup, ← B.contact]; exact hselF
      exact D.strict_selected_rightUnique hs hselF'
    have hvp : v ≠ B.e.head := by
      intro hvp
      exact hne ⟨D.strict_selected_leftUnique hs (hvp ▸ hselE), hvp⟩
    have hvq : v ≠ D.area.next B.e.head := fun h => hvg (h.trans B.head.symm)
    rwa [Equiv.swap_apply_of_ne_of_ne hup huq, Equiv.swap_apply_of_ne_of_ne hvp hvq]
  · change u = B.e.tail at hu
    change v = D.area.next B.e.head at hv
    subst hu hv
    rw [Equiv.swap_apply_of_ne_of_ne hetp hetq, Equiv.swap_apply_right]
    exact hselE
  · change u = D.area.next B.f.tail at hu
    change v = B.f.head at hv
    subst hu hv
    rw [B.contact, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hfhp hfhq,
      ← B.contact]
    exact hselF

theorem resolved_admissible (ht : D.EligibleDE t) (ha : D.edgeData.Admissible ∅) :
    B.resolved.edgeData.Admissible ∅ := by
  intro v hv
  exact ha _ (Relation.TransGen.lift _ (fun _ _ h => B.resolved_selected_swap ht h) _ _ hv)

end DDLocalData
end VerticalStripLLT.Circular.Diagram


