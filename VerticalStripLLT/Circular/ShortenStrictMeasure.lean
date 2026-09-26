import VerticalStripLLT.Circular.GeometricArea
import VerticalStripLLT.Circular.ShortenStrictPairs

/-! The NN target decreases the author's doubled geometric area by two. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular
namespace Diagram

open scoped BigOperators Classical

variable {n : ℕ} (D : Diagram n) (e : Edge D.area) (he : e ∈ D.strict)
  (hlen : 2 ≤ e.length.val)
  (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)

theorem shortenStrict_strict_card :
    (D.shortenStrict e he hlen hgap).strict.card = D.strict.card := by
  let Q := D.shortenStrict e he hlen hgap
  let f := D.shortenedOldEdge e he hlen
  have hmem : (e.tail, e.head) ∈ D.pairGraph.strictEdges :=
    (D.mem_pairGraph_strict_iff _).mpr ⟨e, he, rfl⟩
  have hn : (f.tail, f.head) ∉ D.pairGraph.strictEdges.erase (e.tail, e.head) := by
    intro h
    obtain ⟨g, hg, hp⟩ := (D.mem_pairGraph_strict_iff _).mp (Finset.mem_erase.mp h).2
    have hgf : g = f := D.endpointEmbedding.injective hp
    apply D.shortened_old_edge_not_strict e he hlen
    change f ∈ D.strict
    rwa [← hgf]
  have hcard := congrArg Finset.card (D.shortenStrict_pairGraph_strictEdges e he hlen hgap)
  change Q.pairGraph.strictEdges.card =
    (insert (f.tail, f.head) (D.pairGraph.strictEdges.erase (e.tail, e.head))).card at hcard
  rw [Finset.card_insert_of_notMem hn, Finset.card_erase_of_mem hmem] at hcard
  have hQ : Q.pairGraph.strictEdges.card = Q.strict.card := Finset.card_map _
  have hD : D.pairGraph.strictEdges.card = D.strict.card := Finset.card_map _
  have hpos : 0 < D.pairGraph.strictEdges.card := Finset.card_pos.mpr ⟨_, hmem⟩
  rw [hQ, hD] at hcard
  rw [hD] at hpos
  lia

theorem shortenStrict_area_sum :
    (∑ i, (D.shortenStrict e he hlen hgap).area.area i) + 1 = ∑ i, D.area.area i := by
  let Q := D.shortenStrict e he hlen hgap
  have hpos := corner_area_pos (D.strict_corner e he)
  have hp (i : Fin n) : Q.area.area i + (if i = e.head then 1 else 0) = D.area.area i := by
    change Function.update D.area.area e.head (D.area.area e.head - 1) i + _ = _
    by_cases hi : i = e.head
    · subst i
      simp only [Function.update_self, ↓reduceIte]
      lia
    · rw [Function.update_of_ne hi]
      simp only [hi, ↓reduceIte, add_zero]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hp i)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using hs

theorem shortenStrict_doubledArea :
    (D.shortenStrict e he hlen hgap).doubledArea + 2 = D.doubledArea := by
  let Q := D.shortenStrict e he hlen hgap
  have hs := D.shortenStrict_area_sum e he hlen hgap
  have hc := D.shortenStrict_strict_card e he hlen hgap
  have hbound := Q.strict_card_le_area_sum
  unfold doubledArea
  change 2 * (∑ i, Q.area.area i) - Q.strict.card + 2 =
    2 * (∑ i, D.area.area i) - D.strict.card
  change (∑ i, Q.area.area i) + 1 = ∑ i, D.area.area i at hs
  change Q.strict.card = D.strict.card at hc
  lia

theorem shortenStrict_doubledArea_lt :
    (D.shortenStrict e he hlen hgap).doubledArea < D.doubledArea := by
  have := D.shortenStrict_doubledArea e he hlen hgap
  lia

end Diagram
end VerticalStripLLT.Circular
