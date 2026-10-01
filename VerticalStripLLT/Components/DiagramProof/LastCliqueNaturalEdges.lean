import VerticalStripLLT.Components.DiagramProof.NaturalSeparators
import VerticalStripLLT.Components.DiagramProof.LastCliqueDiagram

/-! Short natural edges in the core ending at a last-clique vertex. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical CornerFamily

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- The core on `0, ..., c, e` inherits every natural edge of length at most two. -/
theorem lastClique_induced_short_naturalEdges (hD : Forward D)
    (hshort : ∀ u v : Fin n, u < v → v.val ≤ u.val + 2 →
      naturalEdgeRelation (D := D) u v)
    (c e : Fin n) (hce : c < e) (g : Edge D.area)
    (hgt : g.tail < c) (hgh : g.head = e) :
    ∀ u v : Fin (c.val + 2), u < v → v.val ≤ u.val + 2 →
      naturalEdgeRelation (D := inducedDiagram hD (lastCliqueEmbed c e hce)) u v := by
  intro u v huv hgap
  let ι := lastCliqueEmbed c e hce
  apply (inducedDiagram_naturalEdge_iff hD ι u v).mpr
  by_cases hv : v.val ≤ c.val
  · have hu : u.val ≤ c.val := by
      have huv' : u.val < v.val := huv
      exact huv'.le.trans hv
    obtain ⟨q, hqt, hqh⟩ := hshort (ι u) (ι v) (ι.strictMono huv) (by
      rw [lastCliqueEmbed_of_le c e hce u hu, lastCliqueEmbed_of_le c e hce v hv]
      exact hgap)
    exact ⟨q, hqt, hqh⟩
  · have hv' : c.val < v.val := lt_of_not_ge hv
    have hvlast : v = Fin.last (c.val + 1) := by
      apply Fin.ext
      change v.val = c.val + 1
      have := v.isLt
      lia
    have hu : u.val ≤ c.val := by
      rw [hvlast] at huv
      change u.val < c.val + 1 at huv
      lia
    have hcu : c.val - 1 ≤ u.val := by
      rw [hvlast] at hgap
      change c.val + 1 ≤ u.val + 2 at hgap
      lia
    have htail : g.tail ≤ ι u := by
      rw [lastCliqueEmbed_of_le c e hce u hu]
      change g.tail.val ≤ u.val
      have hgc : g.tail.val ≤ c.val - 1 := by
        change g.tail.val < c.val at hgt
        lia
      exact hgc.trans hcu
    have hue : ι u < e := by
      rw [← lastCliqueEmbed_last c e hce, ← hvlast]
      exact ι.strictMono huv
    have hnat : naturalEdgeRelation (D := D) (ι u) e :=
      naturalEdgeRelation_of_le_of_le hD ⟨g, rfl, hgh⟩ htail hue (by rw [← hgh])
    rw [hvlast, lastCliqueEmbed_last]
    exact hnat

end

end VerticalStripLLT.Circular.DiagramProof
