import VerticalStripLLT.Components.DiagramProof.CornerChains
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! The retained corner chains form a forest. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- A forward relation with unique predecessors has acyclic symmetrization. -/
theorem isAcyclic_fromRel_of_forward_of_leftUnique
    {V : Type*} [LinearOrder V] {R : V → V → Prop}
    (hforward : ∀ ⦃u v⦄, R u v → u < v)
    (hleft : Relator.LeftUnique R) :
    (SimpleGraph.fromRel R).IsAcyclic := by
  intro v c hc
  let s : Finset V := c.support.toFinset
  have hs : s.Nonempty := by
    exact ⟨v, List.mem_toFinset.mpr (c.end_mem_support)⟩
  let m : V := s.max' hs
  have hm : m ∈ c.support := by
    exact List.mem_toFinset.mp (s.max'_mem hs)
  let d : (SimpleGraph.fromRel R).Walk m m := c.rotate m hm
  have hd : d.IsCycle := hc.rotate hm
  have hmax : ∀ x ∈ c.support, x ≤ m := by
    intro x hx
    exact Finset.le_max' s x (List.mem_toFinset.mpr hx)
  have hmem_snd : d.snd ∈ c.support := by
    apply (c.mem_support_rotate_iff m hm).mp
    exact List.mem_of_mem_tail (d.snd_mem_tail_support hd.not_nil)
  have hmem_pen : d.penultimate ∈ c.support := by
    apply (c.mem_support_rotate_iff m hm).mp
    exact List.mem_of_mem_dropLast (d.penultimate_mem_dropLast_support hd.not_nil)
  have hsnd_le : d.snd ≤ m := hmax d.snd hmem_snd
  have hpen_le : d.penultimate ≤ m := hmax d.penultimate hmem_pen
  have hsnd : (SimpleGraph.fromRel R).Adj m d.snd := d.adj_snd hd.not_nil
  have hpen : (SimpleGraph.fromRel R).Adj d.penultimate m :=
    d.adj_penultimate hd.not_nil
  have hsndR : R d.snd m := by
    rcases (SimpleGraph.fromRel_adj R m d.snd).mp hsnd with ⟨_, hR | hR⟩
    · exact (not_le_of_gt (hforward hR) hsnd_le).elim
    · exact hR
  have hpenR : R d.penultimate m := by
    rcases (SimpleGraph.fromRel_adj R d.penultimate m).mp hpen with ⟨_, hR | hR⟩
    · exact hR
    · exact (not_le_of_gt (hforward hR) hpen_le).elim
  exact hd.snd_ne_penultimate (hleft hsndR hpenR)

namespace CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D)

theorem stepGraph_isAcyclic (hforward : Forward D) :
    (SimpleGraph.fromRel (F.step)).IsAcyclic :=
  isAcyclic_fromRel_of_forward_of_leftUnique
    (fun {_ _} h => F.step_forward hforward h)
    F.step_leftUnique

end CornerFamily

end

end VerticalStripLLT.Circular.DiagramProof
