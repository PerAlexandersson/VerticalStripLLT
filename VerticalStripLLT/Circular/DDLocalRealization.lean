import VerticalStripLLT.Circular.DDLocalData

/-! Realize an actual eligible DD search as concrete last-contact resolution data. -/

namespace VerticalStripLLT.Circular.Diagram

variable {n : ℕ} (D : Diagram n)

theorem exists_ddLocalData {t x : ℤ} {k : ℕ}
    (ht : D.EligibleDE t) (h : ReverseBounceN D t x (k + 1)) :
    Nonempty (D.DDLocalData t) := by
  obtain ⟨hz, hc, hc1, _⟩ := D.reverseBounceN_succ_iff.mp h
  obtain ⟨e, he, eh⟩ := hc
  obtain ⟨f, hf, fh⟩ := ht.1
  obtain ⟨g, hg, gh⟩ := hc1
  have hcontact : f.tail = e.head := (D.strictEdge_tail_of_lift hf fh).trans eh.symm
  have hhead : g.head = D.area.next e.head := by rw [gh, D.residue_succ, eh]
  have hlen : 2 ≤ f.length.val := by
    rw [(D.strict_corner f hf).1, fh]
    exact ht.2.1
  have hn : 3 ≤ n := by have := f.length_lt_n; lia
  have hfe : f ≠ e := by
    intro hfe
    exact f.tail_ne_head (hcontact.trans (congrArg Edge.head hfe).symm)
  have heg : e ≠ g := by
    intro heq
    apply D.residue_p_ne_succ (by lia) (D.boundary t)
    exact eh.symm.trans ((congrArg Edge.head heq).trans gh)
  have hfg : f ≠ g := by
    intro heq
    have hsame : D.residue t = D.residue (D.boundary t + 1) :=
      fh.symm.trans ((congrArg Edge.head heq).trans gh)
    have hl := ht.2.1
    have hb := D.area.bound (D.residue t)
    have heq' := D.eq_of_residue_eq_of_bounds hsame
      (by unfold boundary; lia) (by unfold boundary; lia)
    unfold boundary at heq'
    lia
  have hs : D.area.area (D.area.next e.head) = D.area.area e.head := by
    rw [eh]
    exact D.strict_zero_gap_area_eq ⟨e, he, eh⟩ hz
  have hb : D.area.area e.head + 1 < n := by
    by_contra hh
    have hbound := D.area.bound e.head
    have hfull : (D.area.area (D.residue (D.boundary t)) : ℤ) + 1 = n := by
      rw [← eh]
      lia
    have hbb : D.boundary (D.boundary t) = D.boundary t + 1 + (n : ℤ) * (-1) := by
      rw [boundary]
      lia
    have hstep := D.selected_of_strictAt (show D.strictAt (D.boundary t) from ⟨e, he, eh⟩)
    rw [hbb, D.residue_add_period] at hstep
    exact ht.parallel_end_free D _ hstep
  have hgap : D.area.area (D.area.next f.head) < D.area.area f.head := by
    have hh := ht.boundary_gap D
    simp only [boundary, D.residue_succ, ← fh] at hh
    lia
  exact ⟨⟨e, f, g, he, hf, hg, eh, fh, gh, hfe, heg, hfg, hcontact,
    hhead, hs, hb, hlen, hgap⟩⟩

end VerticalStripLLT.Circular.Diagram
