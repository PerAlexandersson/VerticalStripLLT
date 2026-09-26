import VerticalStripLLT.Circular.ForcedColoring
import VerticalStripLLT.Circular.ForcedOrientation
import VerticalStripLLT.Circular.DNTargetPairs
import VerticalStripLLT.Circular.FirstBounceRecurrences

/-! A common forced-edge factor for the two independently defined LLT expressions. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped BigOperators Classical

variable {n : ℕ} (D : Diagram n)

theorem coloringLLT_forced_edge (e : Edge D.area)
    (he : e ∈ D.edgeData.normalEdges)
    (hpath : Relation.TransGen (D.edgeData.selected ∅) e.tail e.head) (m : ℕ) :
    D.coloringLLT m = MvPolynomial.C Polynomial.X *
      (D.pairGraph.eraseNormal (e.tail, e.head)).coloringLLT m := by
  rw [← D.pairGraph_coloringLLT]
  apply D.pairGraph.coloringLLT_eraseNormal_forced (e.tail, e.head)
  · exact (D.mem_pairGraph_normal_iff _).mpr ⟨e, he, rfl⟩
  · exact Relation.TransGen.mono
      (fun _ _ h => (D.selected_empty_iff_pair_strict _ _).mp h) _ _ hpath

theorem xQShift_coloringLLT_forced_edge (e : Edge D.area)
    (he : e ∈ D.edgeData.normalEdges)
    (hpath : Relation.TransGen (D.edgeData.selected ∅) e.tail e.head) (m : ℕ) :
    xQShift m (D.coloringLLT m) = MvPolynomial.C (Polynomial.X + 1) *
      xQShift m ((D.pairGraph.eraseNormal (e.tail, e.head)).coloringLLT m) := by
  rw [D.coloringLLT_forced_edge e he hpath m, map_mul]
  congr 1
  simpa using xQShift_C_X_pow' m 1

/-- Cancellation reduces the semantic bridge to the exact punctured expressions. -/
theorem expansion_iff_forced_edge (e : Edge D.area)
    (he : e ∈ D.edgeData.normalEdges)
    (hpath : Relation.TransGen (D.edgeData.selected ∅) e.tail e.head) (m : ℕ) :
    (xQShift m (D.coloringLLT m) = evalElementary m (shiftedOrientationExpansion D)) ↔
      xQShift m ((D.pairGraph.eraseNormal (e.tail, e.head)).coloringLLT m) =
        evalElementary m (∑ A ∈ (D.edgeData.normalEdges.erase e).powerset,
          MvPolynomial.C (Polynomial.X ^ A.card) * D.orientMono A) := by
  rw [D.xQShift_coloringLLT_forced_edge e he hpath m,
    D.shiftedOrientationExpansion_forced_edge e he hpath, map_mul, evalElementary_C]
  have hq : (MvPolynomial.C (Polynomial.X + 1) : XPoly m) ≠ 0 := by
    intro h
    have hp : (Polynomial.X + 1 : Polynomial ℤ) = 0 :=
      MvPolynomial.C_injective (Fin m) (Polynomial ℤ) (by simpa only [map_zero] using h)
    have hv := congrArg (Polynomial.eval (0 : ℤ)) hp
    norm_num at hv
  exact ⟨mul_left_cancel₀ hq, congrArg (fun a => MvPolynomial.C (Polynomial.X + 1) * a)⟩

end VerticalStripLLT.Circular.Diagram
