import VerticalStripLLT.Components.DiagramProof.QuotientOccupancy
import VerticalStripLLT.Components.DiagramProof.ChainQuotient
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Terminal-copy insertion and erasure on the chain quotient. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical
open SimpleGraph

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

private theorem terminal_edges_eq_of_same_endpoints {e f : Edge D.area}
    (he : e ∈ F.terminalEdges hforward) (hf : f ∈ F.terminalEdges hforward)
    (ht : F.terminal hforward e.tail = F.terminal hforward f.tail)
    (hh : F.terminal hforward e.head = F.terminal hforward f.head) : e = f :=
  F.terminalEdges_label_injective hforward he hf (Prod.ext ht hh)

private theorem terminal_edges_not_reverse {e f : Edge D.area}
    (he : e ∈ F.terminalEdges hforward) (hf : f ∈ F.terminalEdges hforward)
    (ht : F.terminal hforward e.tail = F.terminal hforward f.head)
    (hh : F.terminal hforward e.head = F.terminal hforward f.tail) : False := by
  have het := (F.mem_terminalEdges hforward e).mp he
  have hft := (F.mem_terminalEdges hforward f).mp hf
  rw [het.1, hft.2] at ht
  rw [het.2, hft.1] at hh
  have hlt := hforward e
  rw [ht, hh] at hlt
  exact (not_lt_of_ge (hforward f).le) hlt

/-- Terminal copies determine their unordered pair of chain vertices injectively. -/
theorem terminal_pair_eq_iff {p f : Edge D.area}
    (hp : p ∈ F.terminalEdges hforward) (hf : f ∈ F.terminalEdges hforward) :
    s(F.chainVertex hforward p.tail, F.chainVertex hforward p.head) =
        s(F.chainVertex hforward f.tail, F.chainVertex hforward f.head) ↔
      p = f := by
  constructor
  · intro h
    rcases Sym2.eq_iff.mp h with hsame | hreverse
    · apply F.terminal_edges_eq_of_same_endpoints hforward hp hf
      · exact congrArg Subtype.val hsame.1
      · exact congrArg Subtype.val hsame.2
    · exact (F.terminal_edges_not_reverse hforward hp hf
        (congrArg Subtype.val hreverse.1)
        (congrArg Subtype.val hreverse.2)).elim
  · rintro rfl
    rfl

private theorem chainQuotient_erase_terminal (A : Finset (Edge D.area))
    (hA : A ⊆ F.terminalEdges hforward) (e : Edge D.area)
    (he : e ∈ F.terminalEdges hforward) :
    F.chainQuotient hforward (A.erase e) =
      (F.chainQuotient hforward A).deleteEdges
        {s(F.chainVertex hforward e.tail, F.chainVertex hforward e.head)} := by
  ext B C
  rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hne, h | h⟩
    · obtain ⟨g, hg, ht, hh⟩ := h
      refine ⟨⟨hne, Or.inl ⟨g, Finset.mem_of_mem_erase hg, ht, hh⟩⟩, ?_⟩
      intro hpair
      rcases Sym2.eq_iff.mp hpair with hsame | hreverse
      · apply Finset.ne_of_mem_erase hg
        apply F.terminal_edges_eq_of_same_endpoints hforward (hA (Finset.mem_of_mem_erase hg))
          he
        · exact ht.trans (congrArg Subtype.val hsame.1)
        · exact hh.trans (congrArg Subtype.val hsame.2)
      · exact F.terminal_edges_not_reverse hforward (hA (Finset.mem_of_mem_erase hg)) he
          (ht.trans (congrArg Subtype.val hreverse.1))
          (hh.trans (congrArg Subtype.val hreverse.2))
    · obtain ⟨g, hg, ht, hh⟩ := h
      refine ⟨⟨hne, Or.inr ⟨g, Finset.mem_of_mem_erase hg, ht, hh⟩⟩, ?_⟩
      intro hpair
      rcases Sym2.eq_iff.mp hpair with hsame | hreverse
      · exact F.terminal_edges_not_reverse hforward (hA (Finset.mem_of_mem_erase hg)) he
          (ht.trans (congrArg Subtype.val hsame.2))
          (hh.trans (congrArg Subtype.val hsame.1))
      · apply Finset.ne_of_mem_erase hg
        apply F.terminal_edges_eq_of_same_endpoints hforward (hA (Finset.mem_of_mem_erase hg))
          he
        · exact ht.trans (congrArg Subtype.val hreverse.2)
        · exact hh.trans (congrArg Subtype.val hreverse.1)
  · rintro ⟨hQ, hnepair⟩
    rcases hQ with ⟨hne, h | h⟩
    · obtain ⟨g, hg, ht, hh⟩ := h
      have hge : g ≠ e := by
        intro hge
        apply hnepair
        subst g
        apply Sym2.eq_iff.mpr
        exact Or.inl ⟨Subtype.ext ht.symm, Subtype.ext hh.symm⟩
      exact ⟨hne, Or.inl ⟨g, Finset.mem_erase.mpr ⟨hge, hg⟩, ht, hh⟩⟩
    · obtain ⟨g, hg, ht, hh⟩ := h
      have hge : g ≠ e := by
        intro hge
        apply hnepair
        subst g
        apply Sym2.eq_iff.mpr
        exact Or.inr ⟨Subtype.ext hh.symm, Subtype.ext ht.symm⟩
      exact ⟨hne, Or.inr ⟨g, Finset.mem_erase.mpr ⟨hge, hg⟩, ht, hh⟩⟩

private theorem chainQuotient_insert_terminal (A : Finset (Edge D.area))
    (f : Edge D.area) :
    F.chainQuotient hforward (insert f A) =
      F.chainQuotient hforward A ⊔
        SimpleGraph.edge (F.chainVertex hforward f.tail) (F.chainVertex hforward f.head) := by
  ext B C
  constructor
  · rintro ⟨hne, h | h⟩
    · obtain ⟨g, hg, ht, hh⟩ := h
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact Or.inr (by
          rw [SimpleGraph.edge_adj]
          exact ⟨Or.inl ⟨Subtype.ext ht.symm, Subtype.ext hh.symm⟩, hne⟩)
      · exact Or.inl ⟨hne, Or.inl ⟨g, hg, ht, hh⟩⟩
    · obtain ⟨g, hg, ht, hh⟩ := h
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact Or.inr (by
          rw [SimpleGraph.edge_adj]
          exact ⟨Or.inr ⟨Subtype.ext hh.symm, Subtype.ext ht.symm⟩, hne⟩)
      · exact Or.inl ⟨hne, Or.inr ⟨g, hg, ht, hh⟩⟩
  · rintro (h | h)
    · rcases h with ⟨hne, h | h⟩
      · obtain ⟨g, hg, ht, hh⟩ := h
        exact ⟨hne, Or.inl ⟨g, Finset.mem_insert_of_mem hg, ht, hh⟩⟩
      · obtain ⟨g, hg, ht, hh⟩ := h
        exact ⟨hne, Or.inr ⟨g, Finset.mem_insert_of_mem hg, ht, hh⟩⟩
    · rw [SimpleGraph.edge_adj] at h
      rcases h with ⟨hsame | hreverse, hne⟩
      · exact ⟨hne, Or.inl ⟨f, Finset.mem_insert_self _ _,
          congrArg Subtype.val hsame.1.symm, congrArg Subtype.val hsame.2.symm⟩⟩
      · exact ⟨hne, Or.inr ⟨f, Finset.mem_insert_self _ _,
          congrArg Subtype.val hreverse.2.symm, congrArg Subtype.val hreverse.1.symm⟩⟩

/-- Erasing one terminal copy and inserting another performs the same operation on its
chain quotient graph. -/
theorem chainQuotient_terminal_insert_erase (A : Finset (Edge D.area))
    (hA : A ⊆ F.terminalEdges hforward) (e f : Edge D.area)
    (he : e ∈ F.terminalEdges hforward) :
    F.chainQuotient hforward (insert f (A.erase e)) =
      (F.chainQuotient hforward A).deleteEdges
        {s(F.chainVertex hforward e.tail, F.chainVertex hforward e.head)} ⊔
      SimpleGraph.edge (F.chainVertex hforward f.tail) (F.chainVertex hforward f.head) := by
  rw [F.chainQuotient_insert_terminal hforward, F.chainQuotient_erase_terminal hforward A hA e he]

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
