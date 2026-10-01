import VerticalStripLLT.Components.DiagramProof.InitialVertex.Copies
import VerticalStripLLT.Components.DiagramProof.InitialVertex.Counts

/-! The extra initial edges and their matching good edges in the actual retained core. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

noncomputable section

variable {k : ℕ} {D : Diagram (k + 2)}

/-- The good initial row consists of its corner and exactly the terminal-increasing extras. -/
theorem initialVertex_good_edge_iff (F : CornerFamily D) (hD : Forward D)
    (f e : Edge D.area) (hf : f ∈ F.edges) (ht : e.tail = f.tail) :
    F.GoodEdge hD e ↔ e = f ∨
      e.head < f.head ∧ F.terminal hD f.head < F.terminal hD e.head := by
  have hterm : F.terminal hD e.tail = F.terminal hD f.head := by
    rw [ht]
    exact F.terminal_eq_of_step hD ((F.step_iff _ _).mpr ⟨f, hf, rfl, rfl⟩)
  constructor
  · intro he
    by_cases hef : e = f
    · exact Or.inl hef
    · have hhead : e.head < f.head := lt_of_le_of_ne
        (F.head_le_of_same_tail hD hf ht) (fun hh =>
          hef (D.endpointEmbedding.injective (Prod.ext ht hh)))
      have hen : e ∉ F.edges := by
        intro heF
        have hh := F.step_rightUnique
          ((F.step_iff _ _).mpr ⟨e, heF, rfl, rfl⟩)
          ((F.step_iff _ _).mpr ⟨f, hf, ht.symm, rfl⟩)
        exact hhead.ne hh
      exact Or.inr ⟨hhead, hterm ▸ he.resolve_left hen⟩
  · rintro (rfl | ⟨_, hgood⟩)
    · exact Or.inl hf
    · exact Or.inr (hterm.symm ▸ hgood)

/-- The matching copy is an actual normal good edge in the core, not merely an ambient edge. -/
theorem exists_initial_matching_core_edge (F : CornerFamily D) (hD : Forward D)
    (f e : Edge D.area) (hf : f ∈ F.edges) (hft : f.tail = 0)
    (het : e.tail = 0) (hegood : F.terminal hD e.tail < F.terminal hD e.head) :
    ∃ d : Edge (inducedDiagram hD (Fin.succOrderEmb (k + 1))).area,
      F.CopyLink e (inducedEdge hD (Fin.succOrderEmb (k + 1)) d) ∧
      (inducedEdge hD (Fin.succOrderEmb (k + 1)) d).tail = f.head ∧
      d ∉ (F.induced hD (Fin.succOrderEmb (k + 1))).edges ∧
      (F.induced hD (Fin.succOrderEmb (k + 1))).GoodEdge
        (inducedDiagram_forward hD (Fin.succOrderEmb (k + 1))) d ∧
      d ∈ (inducedDiagram hD (Fin.succOrderEmb (k + 1))).edgeData.normalEdges := by
  let ι := Fin.succOrderEmb (k + 1)
  obtain ⟨q, hqt, hlink, hqn, _, _, hgood, _⟩ :=
    F.exists_initial_matching_edge hD f e hf (het.trans hft.symm) hegood
  have hpos : q.tail ≠ 0 := by
    rw [hqt]
    exact ne_of_gt (by simpa only [hft] using hD f)
  obtain ⟨u, v, hu, hv⟩ := (initialVertex_edge_retained_iff hD q).mpr hpos
  obtain ⟨d, hd⟩ := (mem_range_inducedEdge_iff hD ι q).mpr ⟨u, v, hu, hv⟩
  have hdn : d ∉ (F.induced hD ι).edges := by
    intro hdF
    exact hqn (hd ▸ (F.mem_induced_edges hD ι d).mp hdF)
  refine ⟨d, hd.symm ▸ hlink, hd.symm ▸ hqt, hdn, ?_, ?_⟩
  · apply (F.goodEdge_induced_iff_of_closed hD ι (F.initialVertex_step_closed hD) d).mpr
    exact hd.symm ▸ hgood
  · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun hs => hdn ((F.induced hD ι).contains_strict hs)⟩

end

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
