import VerticalStripLLT.Components.DiagramProof.Basic
import VerticalStripLLT.Components.ShortEdges

/-!
# Natural edges inside a natural interval

A natural lifted edge contains every shorter natural interval between its
endpoints.  We record this directly at the ambient diagram level, and then
give the ordered-subdiagram form used by clique arguments.
-/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- Every ordered pair strictly inside a natural lifted edge is natural. -/
theorem exists_edge_of_naturalLift_of_le {e : Edge D.area} {a b x y : Fin n}
    (he : D.naturalLift e (a.val : ℤ) (b.val : ℤ))
    (hax : a ≤ x) (hxy : x < y) (hyb : y ≤ b) :
    ∃ f : Edge D.area, f.tail = x ∧ f.head = y := by
  have hab : D.boundaryNaturalLift (a.val : ℤ) (b.val : ℤ) :=
    D.boundaryNaturalLift_of_naturalLift he
  have hboundary : D.boundary (y.val : ℤ) ≤ (x.val : ℤ) := by
    have hmon : D.boundary (y.val : ℤ) ≤ D.boundary (b.val : ℤ) := by
      apply D.boundary_monotone
      exact_mod_cast hyb
    have hleft : D.boundary (b.val : ℤ) ≤ (a.val : ℤ) := hab.1
    have hax' : (a.val : ℤ) ≤ (x.val : ℤ) := by exact_mod_cast hax
    exact hmon.trans (hleft.trans hax')
  have hxy' : (x.val : ℤ) < (y.val : ℤ) := by exact_mod_cast hxy
  have hshort : D.boundaryNaturalLift (x.val : ℤ) (y.val : ℤ) :=
    ⟨hboundary, hxy'⟩
  refine ⟨D.edgeFromLift (x.val : ℤ) (y.val : ℤ) hshort, ?_, ?_⟩
  · rw [D.edgeFromLift_tail hshort, Orientation.residue_intCast_eq]
  · rw [D.edgeFromLift_head hshort, Orientation.residue_intCast_eq]

/-- An increasing indexed set inside a natural edge has all its natural edges. -/
theorem exists_edge_of_orderEmbedding_mem_interval {k : ℕ}
    (hforward : Forward D) (e : Edge D.area) (ι : Fin (k + 1) ↪o Fin n)
    (hι : ∀ i, e.tail ≤ ι i ∧ ι i ≤ e.head) {i j : Fin (k + 1)}
    (hij : i < j) :
    ∃ f : Edge D.area, f.tail = ι i ∧ f.head = ι j := by
  have he : D.naturalLift e (e.tail.val : ℤ) (e.head.val : ℤ) :=
    D.naturalLift_of_tail_lt_head e (hforward e)
  apply exists_edge_of_naturalLift_of_le he
  · exact (hι i).1
  · exact ι.strictMono hij
  · exact (hι j).2

end

end VerticalStripLLT.Circular.DiagramProof
