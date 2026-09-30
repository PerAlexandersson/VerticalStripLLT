import VerticalStripLLT.Components.DiagramProof.ParallelPacking

/-! Occupancy updates under one selected-edge exchange. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

variable {I V : Type*}

/-- Filtering by a label records the deletion of `e` and insertion of `f`.
The two labels are assumed distinct. -/
theorem card_filter_insert_erase_label
    (S : Finset V) (labelOf : V → I) (e f : V) (i : I)
    (he : e ∈ S) (hf : f ∉ S)
    (hlabel : labelOf e ≠ labelOf f) :
    ((insert f (S.erase e)).filter (fun v => labelOf v = i)).card =
      if i = labelOf e then
        (S.filter (fun v => labelOf v = i)).card - 1
      else if i = labelOf f then
        (S.filter (fun v => labelOf v = i)).card + 1
      else (S.filter (fun v => labelOf v = i)).card := by
  classical
  by_cases hiE : i = labelOf e
  · have hfi : labelOf f ≠ i := by
      intro h
      exact hlabel (hiE.symm.trans h.symm)
    have hefilt : e ∈ S.filter (fun v => labelOf v = i) :=
      Finset.mem_filter.mpr ⟨he, hiE.symm⟩
    have hfilter :
        (insert f (S.erase e)).filter (fun v => labelOf v = i) =
          (S.filter (fun v => labelOf v = i)).erase e := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨hvS, hvi⟩
        rcases hvS with rfl | ⟨hvne, hvS⟩
        · exact (hfi hvi).elim
        · exact ⟨hvne, hvS, hvi⟩
      · rintro ⟨hvne, hvS, hvi⟩
        exact ⟨Or.inr ⟨hvne, hvS⟩, hvi⟩
    rw [ite_eq_left hiE, hfilter, Finset.card_erase_of_mem hefilt]
  · by_cases hiF : i = labelOf f
    · have hei : labelOf e ≠ i := by
        intro h
        exact hlabel (h.trans hiF)
      have hffilt : f ∉ S.filter (fun v => labelOf v = i) := by
        intro hfilt
        exact hf (Finset.mem_filter.mp hfilt).1
      have hfilter :
          (insert f (S.erase e)).filter (fun v => labelOf v = i) =
            insert f (S.filter (fun v => labelOf v = i)) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨hvS, hvi⟩
          rcases hvS with hv | ⟨hvne, hvS⟩
          · exact Or.inl hv
          · exact Or.inr ⟨hvS, hvi⟩
        · rintro (rfl | ⟨hvS, hvi⟩)
          · exact ⟨Or.inl rfl, hiF.symm⟩
          · refine ⟨Or.inr ⟨?_, hvS⟩, hvi⟩
            intro hve
            subst v
            exact hei hvi
      rw [ite_eq_right hiE, ite_eq_left hiF, hfilter,
        Finset.card_insert_of_notMem hffilt]
    · have hei : labelOf e ≠ i := by
        intro h
        exact hiE h.symm
      have hfi : labelOf f ≠ i := by
        intro h
        exact hiF h.symm
      have hfilter :
          (insert f (S.erase e)).filter (fun v => labelOf v = i) =
            S.filter (fun v => labelOf v = i) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨hvS, hvi⟩
          rcases hvS with rfl | ⟨hvne, hvS⟩
          · exact (hfi hvi).elim
          · exact ⟨hvS, hvi⟩
        · rintro ⟨hvS, hvi⟩
          refine ⟨Or.inr ⟨?_, hvS⟩, hvi⟩
          intro hve
          subst v
          exact hei hvi
      rw [ite_eq_right hiE, ite_eq_right hiF, hfilter]

end VerticalStripLLT.Circular.DiagramProof

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- Occupancies change by one deletion and one insertion under an exchange. -/
theorem occupancy_of_fullSelection_exchange
    (θ η : Orientation D) (e f : Edge D.area)
    (hfull : fullSelection η = insert f ((fullSelection θ).erase e))
    (he : e ∈ fullSelection θ) (hf : f ∉ fullSelection θ)
    (hlabel : F.copyLabel hforward e ≠ F.copyLabel hforward f)
    (p : Fin n × Fin n) :
    F.occupancy hforward η p =
      if p = F.copyLabel hforward e then
        F.occupancy hforward θ p - 1
      else if p = F.copyLabel hforward f then
        F.occupancy hforward θ p + 1
      else F.occupancy hforward θ p := by
  unfold occupancy
  rw [hfull]
  have h := card_filter_insert_erase_label (fullSelection θ)
    (F.copyLabel hforward) e f p he hf hlabel
  split_ifs at h ⊢ <;> convert h using 1 <;> congr 2 <;> ext x <;> simp

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
