import VerticalStripLLT.Components.DiagramProof.NaturalSeparators
import VerticalStripLLT.Components.DiagramProof.InitialVertexRestriction

/-! Short natural edges and deletion connectivity after removing the initial vertex. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical CornerFamily

noncomputable section

variable {k : ℕ} {D : Diagram (k + 2)}

theorem initialVertex_induced_short_naturalEdges
    (hD : Forward D)
    (hshort : ∀ u v : Fin (k + 2), u < v → v.val ≤ u.val + 2 →
      naturalRel D u v) :
    ∀ u v : Fin (k + 1), u < v → v.val ≤ u.val + 2 →
      naturalRel (inducedDiagram hD (Fin.succOrderEmb (k + 1))) u v := by
  intro u v huv hgap
  apply (inducedDiagram_naturalEdge_iff hD (Fin.succOrderEmb (k + 1)) u v).mpr
  obtain ⟨e, ht, hh⟩ := hshort u.succ v.succ (Fin.succ_lt_succ_iff.mpr huv) (by
    change v.val + 1 ≤ u.val + 1 + 2
    lia)
  exact ⟨e, by simpa only [Fin.coe_succOrderEmb] using ht,
    by simpa only [Fin.coe_succOrderEmb] using hh⟩

theorem initialVertex_induced_naturalEdges_connected_of_short
    (hD : Forward D)
    (hshort : ∀ u v : Fin (k + 2), u < v → v.val ≤ u.val + 2 →
      naturalRel D u v) (u v : Fin (k + 1)) :
    Relation.EqvGen
      (naturalRel (inducedDiagram hD (Fin.succOrderEmb (k + 1)))) u v := by
  apply CornerFamily.naturalRel_connected_of_short
  exact initialVertex_induced_short_naturalEdges hD hshort

theorem initialVertex_induced_naturalEdges_delete_of_short
    (hD : Forward D)
    (hshort : ∀ u v : Fin (k + 2), u < v → v.val ≤ u.val + 2 →
      naturalRel D u v) (w u v : Fin (k + 1))
    (hu : u ≠ w) (hv : v ≠ w) :
    Relation.EqvGen (fun x y => x ≠ w ∧ y ≠ w ∧
      naturalRel (inducedDiagram hD (Fin.succOrderEmb (k + 1))) x y) u v := by
  apply CornerFamily.naturalRel_delete_of_short
    (initialVertex_induced_short_naturalEdges hD hshort) w u v hu hv

end

end VerticalStripLLT.Circular.DiagramProof
