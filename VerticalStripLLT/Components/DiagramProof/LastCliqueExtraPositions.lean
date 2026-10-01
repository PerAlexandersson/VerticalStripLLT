import VerticalStripLLT.Components.DiagramProof.LastCliqueEdges
import VerticalStripLLT.Components.DiagramProof.GoodEdges
import VerticalStripLLT.Components.DiagramProof.LastCliqueTree
import VerticalStripLLT.Components.DiagramProof.TerminalClique

/-! The two sets of extra positions used in last-clique inheritance. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k n : ℕ} {D : Diagram n}

/-- Extra positions with both endpoints in the retained core. -/
def lastCliqueCoreExtraPositions (ι : Fin (k + 1) ↪o Fin n)
    (P : Finset (Edge D.area)) : Finset (Edge D.area) :=
  P.filter (fun e => ∃ u v, ι u = e.tail ∧ ι v = e.head)

/-- Extra positions in the last clique, together with the shared position. -/
def lastCliqueRightExtraPositions (g p : Edge D.area)
    (P : Finset (Edge D.area)) : Finset (Edge D.area) :=
  insert p (P.filter (fun e => g.tail ≤ e.tail ∧ e.head ≤ g.head))

/-- Every extra position belongs to the core or to the right-clique pool. -/
theorem lastClique_extra_positions_cover
    (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n) (c : Fin n)
    (g p : Edge D.area)
    (hbefore : ∀ f : Edge D.area, IsCorner f → f ≠ g → f.head ≤ c)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ c ∨ z = g.head)
    (P : Finset (Edge D.area)) (hp : p ∈ P) :
    P = lastCliqueCoreExtraPositions ι P ∪ lastCliqueRightExtraPositions g p P := by
  ext e
  constructor
  · intro he
    apply Finset.mem_union.mpr
    rcases naturalEdge_in_last_clique_or_core hD g c hbefore e with hr | hc
    · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨he, hr⟩))
    · obtain ⟨u, hu⟩ := (himage e.tail).mpr (Or.inl hc.1)
      obtain ⟨v, hv⟩ := (himage e.head).mpr (Or.inl hc.2)
      exact Or.inl (Finset.mem_filter.mpr ⟨he, u, v, hu, hv⟩)
  · intro he
    rcases Finset.mem_union.mp he with hc | hr
    · exact (Finset.mem_filter.mp hc).1
    · rcases Finset.mem_insert.mp hr with rfl | hr
      · exact hp
      · exact (Finset.mem_filter.mp hr).1

/-- The diagram's shared position belongs to both sets of extra positions. -/
theorem lastClique_shared_extra_position
    (ι : Fin (k + 1) ↪o Fin n) (g p : Edge D.area)
    (P : Finset (Edge D.area)) (hp : p ∈ P)
    (hpcore : ∃ u v, ι u = p.tail ∧ ι v = p.head) :
    p ∈ lastCliqueCoreExtraPositions ι P ∩ lastCliqueRightExtraPositions g p P := by
  exact Finset.mem_inter.mpr
    ⟨Finset.mem_filter.mpr ⟨hp, hpcore⟩, Finset.mem_insert_self _ _⟩

/-- Once the last corner and star are fixed, every other right-pool position is internal. -/
theorem lastClique_right_extra_position_cases
    (F : CornerFamily D) (hD : Forward D) (g p : Edge D.area) (hg : g ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ g.head) (A : Finset (Edge D.area)) (hgA : g ∈ A)
    (hstar : ∀ v, g.tail ≤ v → v < g.head → (edgeSetGraph A).Adj v g.head)
    (e : Edge D.area) (he : e ∈ lastCliqueRightExtraPositions g p (F.goodEdges hD \ A)) :
    e = p ∨ g.tail < e.tail ∧ e.head < g.head := by
  rcases Finset.mem_insert.mp he with he | he
  · exact Or.inl he
  obtain ⟨heP, hbounds⟩ := Finset.mem_filter.mp he
  obtain ⟨heG, heA⟩ := Finset.mem_sdiff.mp heP
  have ht : e.tail ≠ g.tail := by
    intro ht
    have heg := F.goodEdge_eq_last_corner_of_tail hD g hg hlast
      ((F.mem_goodEdges hD e).mp heG) ht
    exact heA (heg.symm ▸ hgA)
  have hh : e.head ≠ g.head := by
    intro hh
    apply heA
    apply (edgeSetGraph_adj_iff_mem hD A e).mp
    rw [hh]
    exact hstar _ hbounds.1 (by simpa only [← hh] using hD e)
  exact Or.inr ⟨lt_of_le_of_ne hbounds.1 (Ne.symm ht), lt_of_le_of_ne hbounds.2 hh⟩

/-- For the displayed crossing corners bc and ae, ba is a shared extra position. -/
theorem lastClique_exists_shared_extra_position
    (F : CornerFamily D) (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)
    (g f : Edge D.area) (hg : g ∈ F.edges) (hf : f ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ g.head)
    (hba : f.tail < g.tail) (hac : g.tail < f.head) (hce : f.head < g.head)
    (himage : ∀ z, (∃ w, ι w = z) ↔ z ≤ f.head ∨ z = g.head)
    (A : Finset (Edge D.area)) (hA : (edgeSetGraph A).IsAcyclic)
    (hFA : edgeSetGraph F.edges ≤ edgeSetGraph A)
    (hstar : ∀ v, g.tail ≤ v → v < g.head → (edgeSetGraph A).Adj v g.head) :
    ∃ p : Edge D.area, p.tail = f.tail ∧ p.head = g.tail ∧
      p ∈ lastCliqueCoreExtraPositions ι (F.goodEdges hD \ A) ∩
        lastCliqueRightExtraPositions g p (F.goodEdges hD \ A) := by
  obtain ⟨p, hpt, hph⟩ := exists_edge_of_naturalLift_of_le
    (D.naturalLift_of_tail_lt_head f (hD f)) le_rfl hba hac.le
  have hpG : p ∈ F.goodEdges hD := by
    apply (F.mem_goodEdges hD p).mpr
    right
    rw [hpt, hph, (F.terminal_eq_iff_mem hD f).mpr hf,
      (F.terminal_eq_iff_mem hD g).mpr hg,
      F.terminal_eq_of_last_corner hD g hlast hac,
      F.terminal_eq_of_last_corner hD g hlast (hD g)]
    exact hce
  have hpA : p ∉ A := by
    intro hp
    have hadj := (edgeSetGraph_adj_iff_mem hD A p).mpr hp
    rw [hpt, hph] at hadj
    exact F.last_clique_tree_omits_shared_edge hD g f hf (edgeSetGraph A)
      hA hFA hstar hba hac hce hadj
  have hpcore : ∃ u v, ι u = p.tail ∧ ι v = p.head := by
    obtain ⟨u, hu⟩ := (himage f.tail).mpr (Or.inl (hD f).le)
    obtain ⟨v, hv⟩ := (himage g.tail).mpr (Or.inl hac.le)
    exact ⟨u, v, hu.trans hpt.symm, hv.trans hph.symm⟩
  exact ⟨p, hpt, hph, lastClique_shared_extra_position ι g p _
    (Finset.mem_sdiff.mpr ⟨hpG, hpA⟩) hpcore⟩

end

end VerticalStripLLT.Circular.DiagramProof
