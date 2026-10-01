import VerticalStripLLT.Components.DiagramProof.CopyPaths

/-! The first corner produces the first matching copy. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hD : Forward D)

theorem exists_initial_matching_edge
    (f e : Edge D.area) (hf : f ∈ F.edges) (hte : e.tail = f.tail)
    (hegood : F.terminal hD e.tail < F.terminal hD e.head) :
    ∃ q : Edge D.area,
      q.tail = f.head ∧ F.CopyLink e q ∧ q ∉ F.edges ∧
      F.terminal hD e.tail = F.terminal hD q.tail ∧
      F.terminal hD e.head = F.terminal hD q.head ∧
      F.GoodEdge hD q ∧ q ∈ D.edgeData.normalEdges := by
  have hstep : F.step e.tail f.head :=
    (F.step_iff _ _).mpr ⟨f, hf, hte.symm, rfl⟩
  have hne : e.tail ≠ F.terminal hD e.tail := by
    intro hterm
    have htermf := F.terminal_eq_of_step hD hstep
    have hlt : e.tail < F.terminal hD e.tail := by
      rw [htermf]
      simpa only [hte] using
        (hD f).trans_le (F.le_terminal hD f.head)
    exact hlt.ne hterm
  obtain ⟨q, hlink, hteq, hheq⟩ :=
    F.exists_copySuccessor hD e hegood hne
  have hqtail : q.tail = f.head := by
    apply F.step_rightUnique hlink.1 hstep
  have hqcorner : q ∉ F.edges := (F.copyLink_not_mem hlink).2
  have hqgood : F.GoodEdge hD q := Or.inr (by
    rw [← hteq, ← hheq]
    exact hegood)
  have hqnormal : q ∈ D.edgeData.normalEdges := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun hstrict => hqcorner (F.contains_strict hstrict)⟩
  exact ⟨q, hqtail, hlink, hqcorner, hteq, hheq, hqgood, hqnormal⟩

end

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
