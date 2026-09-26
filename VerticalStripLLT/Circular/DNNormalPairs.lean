import VerticalStripLLT.Circular.RaiseStrictNormalPairs
import VerticalStripLLT.Circular.DNTargetPairs

/-! Normal endpoint pairs for the valid DN successor. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular
namespace Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

variable (e f : Edge D.area) (he : e ∈ D.strict) (hf : f ∈ D.strict) (hne : f ≠ e)
  (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
  (hb : D.area.area e.head + 1 < n)
  (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
  (hlen : 2 ≤ f.length.val)
  (hgap : D.area.area (D.area.next f.head) < D.area.area f.head)

theorem dnSuccessor_pairGraph_normalEdges :
    (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).pairGraph.normalEdges =
      insert (e.tail, e.head)
        (D.pairGraph.normalEdges.erase (D.area.next f.tail, f.head)) := by
  classical
  have hpair_ne : (e.tail, e.head) ≠ (D.area.next f.tail, f.head) := by
    intro h
    apply hne
    apply D.strict_edge_eq_of_head_eq hf he
    exact (congrArg Prod.snd h).symm
  unfold dnSuccessor
  rw [shortenStrict_pairGraph_normalEdges,
    D.raiseStrict_pairGraph_normalEdges e he heq hb hns]
  rw [shortenedOldEdge_tail]
  change (insert (e.tail, e.head) D.pairGraph.normalEdges).erase
      (D.area.next f.tail, f.head) = _
  rw [Finset.erase_insert_of_ne hpair_ne]

end Diagram
end VerticalStripLLT.Circular
