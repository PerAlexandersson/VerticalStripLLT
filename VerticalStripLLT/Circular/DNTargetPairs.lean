import VerticalStripLLT.Circular.DNTarget
import VerticalStripLLT.Circular.RaiseStrictPairs
import VerticalStripLLT.Circular.ShortenStrictPairs

/-! The exact strict relation of the valid DN successor. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular
namespace Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

theorem selected_empty_iff_pair_strict (u v : Fin n) :
    D.edgeData.selected ∅ u v ↔ (u, v) ∈ D.pairGraph.strictEdges := by
  rw [D.mem_pairGraph_strict_iff]
  constructor
  · rintro ⟨e, he, ht, hh⟩
    exact ⟨e, by simpa [Diagram.edgeData] using he, Prod.ext ht hh⟩
  · rintro ⟨e, he, hp⟩
    exact ⟨e, by simpa [Diagram.edgeData] using he,
      congrArg Prod.fst hp, congrArg Prod.snd hp⟩

variable (e f : Edge D.area) (he : e ∈ D.strict) (hf : f ∈ D.strict) (hne : f ≠ e)
  (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
  (hb : D.area.area e.head + 1 < n)
  (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
  (hlen : 2 ≤ f.length.val)
  (hgap : D.area.area (D.area.next f.head) < D.area.area f.head)

theorem dnSuccessor_pairGraph_strictEdges :
    (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).pairGraph.strictEdges =
      insert (D.area.next f.tail, f.head) (insert (e.tail, D.area.next e.head)
        ((D.pairGraph.strictEdges.erase (e.tail, e.head)).erase (f.tail, f.head))) := by
  unfold dnSuccessor
  rw [shortenStrict_pairGraph_strictEdges, shortenedOldEdge_tail,
    D.raiseStrict_pairGraph_strictEdges]
  change insert (D.area.next f.tail, f.head)
    ((insert (e.tail, D.area.next e.head)
      (D.pairGraph.strictEdges.erase (e.tail, e.head))).erase (f.tail, f.head)) = _
  rw [Finset.erase_insert_of_ne (show (e.tail, D.area.next e.head) ≠ (f.tail, f.head) from
    fun h => hns f hf (congrArg Prod.snd h).symm)]

theorem dnSuccessor_selected_iff (u v : Fin n) :
    (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).edgeData.selected ∅ u v ↔
      (D.edgeData.selected ∅ u v ∧ ¬ (u = e.tail ∧ v = e.head) ∧
        ¬ (u = f.tail ∧ v = f.head)) ∨
      (u = e.tail ∧ v = D.area.next e.head) ∨
      (u = D.area.next f.tail ∧ v = f.head) := by
  rw [selected_empty_iff_pair_strict, D.dnSuccessor_pairGraph_strictEdges,
    D.selected_empty_iff_pair_strict]
  simp only [Finset.mem_insert, Finset.mem_erase, ne_eq, Prod.mk.injEq]
  tauto

end Diagram
end VerticalStripLLT.Circular
