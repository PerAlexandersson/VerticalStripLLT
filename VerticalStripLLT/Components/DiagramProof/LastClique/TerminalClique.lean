import VerticalStripLLT.Components.DiagramProof.LastClique.ParallelPacking
import VerticalStripLLT.Components.DiagramProof.Corners.CliqueEdges

/-! The terminal copies in the last natural clique. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- Natural edges whose two endpoints are terminal vertices of retained chains. -/
noncomputable def terminalEdges : Finset (Edge D.area) :=
  Finset.univ.filter fun e =>
    F.terminal hforward e.tail = e.tail ∧ F.terminal hforward e.head = e.head

@[simp] theorem mem_terminalEdges (e : Edge D.area) :
    e ∈ F.terminalEdges hforward ↔
      F.terminal hforward e.tail = e.tail ∧ F.terminal hforward e.head = e.head := by
  simp only [terminalEdges, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every terminal copy is good and is not a retained corner. -/
theorem terminalEdge_good_not_corner {e : Edge D.area} (he : e ∈ F.terminalEdges hforward) :
    e ∈ F.goodEdges hforward ∧ e ∉ F.edges := by
  obtain ⟨ht, hh⟩ := (F.mem_terminalEdges hforward e).mp he
  have hlt : F.terminal hforward e.tail < F.terminal hforward e.head := by
    simpa only [ht, hh] using hforward e
  exact ⟨(F.mem_goodEdges hforward e).mpr (Or.inr hlt), fun h =>
    hlt.ne ((F.terminal_eq_iff_mem hforward e).mpr h)⟩

/-- An ordered pair of chains has at most one terminal copy. -/
theorem terminalEdges_label_injective {e f : Edge D.area}
    (he : e ∈ F.terminalEdges hforward) (hf : f ∈ F.terminalEdges hforward)
    (hlabel : F.copyLabel hforward e = F.copyLabel hforward f) : e = f := by
  obtain ⟨het, heh⟩ := (F.mem_terminalEdges hforward e).mp he
  obtain ⟨hft, hfh⟩ := (F.mem_terminalEdges hforward f).mp hf
  apply D.endpointEmbedding.injective
  change (e.tail, e.head) = (f.tail, f.head)
  simpa only [copyLabel, het, heh, hft, hfh] using hlabel

/-- A retained corner label cannot be the label of a terminal copy. -/
theorem corner_label_ne_terminalEdge {e f : Edge D.area} (he : e ∈ F.edges)
    (hf : f ∈ F.terminalEdges hforward) :
    F.copyLabel hforward e ≠ F.copyLabel hforward f := by
  intro hlabel
  have hdiag := (F.terminal_eq_iff_mem hforward e).mpr he
  have ht := congrArg Prod.fst hlabel
  have hh := congrArg Prod.snd hlabel
  have hfdiag : F.terminal hforward f.tail = F.terminal hforward f.head :=
    ht.symm.trans (hdiag.trans hh)
  exact (F.terminalEdge_good_not_corner hforward hf).2
    ((F.terminal_eq_iff_mem hforward f).mp hfdiag)

/-- Every vertex strictly to the right of the last corner tail is a chain terminal. -/
theorem terminal_eq_of_last_corner (e : Edge D.area)
    (hlast : ∀ v : Fin n, v ≤ e.head) {v : Fin n} (hav : e.tail < v) :
    F.terminal hforward v = v := by
  by_contra h
  obtain ⟨w, hvw⟩ := F.exists_successor hforward (Ne.symm h)
  obtain ⟨f, hf, hft, _⟩ := (F.step_iff _ _).mp hvw
  have ht := F.corner_tail_le_of_head_le hforward (f := e) hf (hlast f.head)
  rw [hft] at ht
  exact not_le_of_gt hav ht

/-- A good edge starting at the last corner tail is that corner itself. -/
theorem goodEdge_eq_last_corner_of_tail (e : Edge D.area) (he : e ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ e.head) {f : Edge D.area}
    (hf : F.GoodEdge hforward f) (ht : f.tail = e.tail) : f = e := by
  have hterm : F.terminal hforward e.tail = e.head :=
    ((F.terminal_eq_iff_mem hforward e).mpr he).trans
      (F.terminal_eq_of_last_corner hforward e hlast (hforward e))
  rcases hf with hf | hf
  · apply D.endpointEmbedding.injective
    refine Prod.ext ht ?_
    exact F.step_rightUnique
      ((F.step_iff e.tail f.head).mpr ⟨f, hf, ht, rfl⟩)
      ((F.step_iff e.tail e.head).mpr ⟨e, he, rfl, rfl⟩)
  · rw [ht, hterm] at hf
    exact (not_le_of_gt hf (hlast (F.terminal hforward f.head))).elim

/-- If the last clique contains all chain terminals, every pair of chains
has its terminal copy in that clique. -/
theorem exists_terminalEdge_of_last_clique (e : Edge D.area)
    (hterm : ∀ v, e.tail < F.terminal hforward v ∧ F.terminal hforward v ≤ e.head)
    (u v : Fin n) (huv : F.terminal hforward u < F.terminal hforward v) :
    ∃ f ∈ F.terminalEdges hforward,
      f.tail = F.terminal hforward u ∧ f.head = F.terminal hforward v := by
  obtain ⟨f, hft, hfh⟩ := exists_edge_of_naturalLift_of_le
    (D.naturalLift_of_tail_lt_head e (hforward e)) (hterm u).1.le huv (hterm v).2
  refine ⟨f, (F.mem_terminalEdges hforward f).mpr ?_, hft, hfh⟩
  simp only [hft, hfh, F.terminal_idempotent hforward, and_self]

/-- Inside the last clique, an anchor consists of its corner and terminal copies. -/
theorem selected_last_clique_iff (e : Edge D.area) (he : e ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ e.head)
    (hterm : ∀ v, e.tail < F.terminal hforward v)
    (θ : Orientation D) (hθ : F.Anchor hforward θ) (f : Edge D.area) :
    (f ∈ fullSelection θ ∧ e.tail ≤ f.tail) ↔
      f = e ∨ (f ∈ fullSelection θ ∧ f ∈ F.terminalEdges hforward) := by
  constructor
  · rintro ⟨hf, htail⟩
    rcases lt_or_eq_of_le htail with hlt | heq
    · right
      refine ⟨hf, (F.mem_terminalEdges hforward f).mpr ⟨?_, ?_⟩⟩
      · exact F.terminal_eq_of_last_corner hforward e hlast hlt
      · exact F.terminal_eq_of_last_corner hforward e hlast (hlt.trans (hforward f))
    · exact Or.inl (F.goodEdge_eq_last_corner_of_tail hforward e he hlast
        (hθ.2 f hf) heq.symm)
  · rintro (rfl | ⟨hf, hterminal⟩)
    · exact ⟨hθ.1 he, le_rfl⟩
    · have ht := ((F.mem_terminalEdges hforward f).mp hterminal).1
      exact ⟨hf, (ht ▸ hterm f.tail).le⟩

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
