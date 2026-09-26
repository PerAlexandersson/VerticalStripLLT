import VerticalStripLLT.Circular.RaiseStrictPairs
import VerticalStripLLT.Circular.EdgeLength
import VerticalStripLLT.Circular.NaturalPairSwap
import Mathlib.Tactic.Linarith

/-! Normal endpoint pairs for the raised DN successor. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular
namespace Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

private theorem raiseStrict_naturalPairs (e : Edge D.area) (he : e ∈ D.strict)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ f ∈ D.strict, f.head ≠ D.area.next e.head) :
    (D.raiseStrict e he heq hb hns).naturalPairs =
      insert (e.tail, D.area.next e.head) D.naturalPairs := by
  classical
  let Q := D.raiseStrict e he heq hb hns
  let r := D.raisedEdge e he heq hb
  ext x
  rw [Finset.mem_insert, Q.mem_naturalPairs_iff, D.mem_naturalPairs_iff]
  constructor
  · rintro ⟨g, hg⟩
    by_cases hgr : g = r
    · left
      rw [hgr] at hg
      exact hg.symm.trans (Prod.ext (D.raisedEdge_tail e he heq hb) rfl)
    · right
      by_cases hh : g.head = D.area.next e.head
      · have hbound : g.length.val ≤ D.area.area e.head + 1 := by
          have h := g.2.2
          change g.length.val ≤
            Function.update D.area.area (D.area.next e.head)
              (D.area.area e.head + 1) g.head at h
          rw [hh, Function.update_self] at h
          exact h
        have hne : g.length.val ≠ e.length.val + 1 := by
          intro hlen
          apply hgr
          apply Subtype.ext
          apply Prod.ext
          · exact hh
          · apply Fin.ext
            exact hlen
        have hcorner := (D.strict_corner e he).1
        have hlt : g.length.val < e.length.val + 1 := by lia
        have hle : g.length.val ≤ D.area.area g.head := by
          rw [hh, heq]
          lia
        let f : Edge D.area :=
          ⟨(g.head, g.length), ⟨g.2.1, hle⟩⟩
        exact ⟨f, hg⟩
      · have hle : g.length.val ≤ D.area.area g.head := by
          have h := g.2.2
          change g.length.val ≤
            Function.update D.area.area (D.area.next e.head)
              (D.area.area e.head + 1) g.head at h
          rw [Function.update_of_ne hh] at h
          exact h
        let f : Edge D.area :=
          ⟨(g.head, g.length), ⟨g.2.1, hle⟩⟩
        exact ⟨f, hg⟩
  · rintro (hx | ⟨f, hf⟩)
    · subst x
      exact ⟨r, Prod.ext (D.raisedEdge_tail e he heq hb) rfl⟩
    · exact ⟨D.raisedIncl e heq hb f, hf⟩

theorem raiseStrict_pairGraph_normalEdges (e : Edge D.area) (he : e ∈ D.strict)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ f ∈ D.strict, f.head ≠ D.area.next e.head) :
    (D.raiseStrict e he heq hb hns).pairGraph.normalEdges =
      insert (e.tail, e.head) D.pairGraph.normalEdges := by
  classical
  let Q := D.raiseStrict e he heq hb hns
  let newPair := (e.tail, D.area.next e.head)
  let oldPair := (e.tail, e.head)
  have hnew : newPair ∉ D.naturalPairs := by
    intro hx
    obtain ⟨f, hf⟩ := (D.mem_naturalPairs_iff newPair).mp hx
    have ht : f.tail = e.tail := congrArg Prod.fst hf
    have hh : f.head = D.area.next e.head := congrArg Prod.snd hf
    have hlen := Edge.length_succ_of_next_head ht hh
    have hbound : f.length.val ≤ D.area.area f.head := f.2.2
    rw [hh, heq, ← (D.strict_corner e he).1] at hbound
    lia
  have holdN : oldPair ∈ D.naturalPairs :=
    (D.mem_naturalPairs_iff oldPair).mpr ⟨e, rfl⟩
  have holdS : oldPair ∈ D.pairGraph.strictEdges := by
    exact (D.mem_pairGraph_strict_iff oldPair).mpr ⟨e, he, rfl⟩
  rw [Q.normalPairs_eq_sdiff, D.normalPairs_eq_sdiff,
    D.raiseStrict_naturalPairs e he heq hb hns,
    D.raiseStrict_pairGraph_strictEdges e he heq hb hns]
  have hno : newPair ≠ oldPair := by
    intro h
    apply hnew
    rw [h]
    exact holdN
  change insert newPair D.naturalPairs \ insert newPair
    (D.pairGraph.strictEdges.erase oldPair) =
      insert oldPair (D.naturalPairs \ D.pairGraph.strictEdges)
  ext x
  by_cases hxn : x = newPair
  · subst x
    simp [hnew, hno]
  · by_cases hxo : x = oldPair
    · subst x
      simp [hxn, holdN, holdS]
    · simp [hxn, hxo]

end Diagram
end VerticalStripLLT.Circular
