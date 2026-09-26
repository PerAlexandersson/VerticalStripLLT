import VerticalStripLLT.Circular.DNContactGeometry
import VerticalStripLLT.Circular.DNTargetPairs
import VerticalStripLLT.Circular.NeutralTermination

/-! Realizing a complete DN contact search as a valid rank-decreasing successor. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular
namespace Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

theorem strictEdge_tail_of_lift {e : Edge D.area} (he : e ∈ D.strict)
    {x : ℤ} (hh : e.head = D.residue x) : e.tail = D.residue (D.boundary x) := by
  apply D.residue_tail_of_length hh
  rw [(D.strict_corner e he).1, hh, boundary]
  ring

theorem strict_zero_gap_area_eq {x : ℤ} (hx : D.strictAt x) (hg : D.eastGap x = 0) :
    D.area.area (D.area.next (D.residue x)) = D.area.area (D.residue x) := by
  simp only [eastGap, hx, ↓reduceIte, boundary, D.residue_succ] at hg
  lia

/-- The neutral branch has a valid successor with the actual two-row area update
and the complete strict-contact witness. No polynomial recurrence is assumed. -/
theorem exists_fullNeutralBounce_of_reverseBounce {t x : ℤ}
    (ha : D.edgeData.Admissible ∅) (ht : D.EligibleDE t)
    (h : ReverseBounce D t x) (hx : D.strictAt x) (hx1 : ¬ D.strictAt (x + 1)) :
    ∃ D' : Diagram n, Nonempty (FullNeutralBounce D D') ∧
      D'.area.area = Function.update
        (Function.update D.area.area (D.residue (x + 1))
          (D.area.area (D.residue x) + 1)) (D.residue t)
            (D.area.area (D.residue t) - 1) ∧
      D'.edgeData.Admissible ∅ ∧ D'.strictRank < D.strictRank := by
  obtain ⟨B⟩ := ReverseBounce.exists_indexed_contacts D h ht.1 hx
  obtain ⟨e, he, eh⟩ := hx
  obtain ⟨f, hf, fh⟩ := ht.1
  have hfe : f ≠ e := by
    intro hh
    exact B.residue_ne ha (eh.symm.trans ((congrArg Edge.head hh).symm.trans fh))
  have heq : D.area.area (D.area.next e.head) = D.area.area e.head := by
    rw [eh]
    exact D.strict_zero_gap_area_eq ⟨e, he, eh⟩ h.terminal_gap.1
  have hb : D.area.area e.head + 1 < n := by
    rw [eh]
    exact B.first_area_bound ha ht hx1
  have hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head := by
    intro g hg hh
    apply hx1
    refine ⟨g, hg, ?_⟩
    rw [hh, eh, D.residue_succ]
  have hlen : 2 ≤ f.length.val := by
    rw [(D.strict_corner f hf).1, fh]
    exact ht.2.1
  have hgap : D.area.area (D.area.next f.head) < D.area.area f.head := by
    have hh := ht.boundary_gap D
    simp only [boundary, D.residue_succ, ← fh] at hh
    lia
  let D' := D.dnSuccessor e f he hf hfe heq hb hns hlen hgap
  have et : e.tail = D.residue (D.boundary x) := D.strictEdge_tail_of_lift he eh
  have ft : f.tail = D.residue (D.boundary t) := D.strictEdge_tail_of_lift hf fh
  have emain : e.head = B.main (0 : Fin (B.k + 1)).succ.castSucc := by
    simpa only [Fin.succ_zero_eq_one, Fin.castSucc_one, B.main_one] using eh
  have fmain : f.tail = B.main (Fin.last B.k).succ.castSucc := by
    simpa only [Fin.succ_last, B.inner_last] using ft
  have epar : D.area.next e.head = B.parallel 0 := by
    rw [eh, ← D.residue_succ, B.parallel_zero]
  have fpar : D.area.next f.tail = B.parallel (Fin.last B.k) := by
    rw [ft, ← D.residue_succ, B.parallel_last]
  let C : FullNeutralBounce D D' := {
    k := B.k
    main := B.main
    parallel := B.parallel
    main_steps := B.main_steps
    parallel_steps := B.parallel_steps
    parallel_next := B.parallel_next
    parallel_start := B.parallel_start_free hx1
    parallel_end := B.parallel_end_free ht
    changed := by
      intro u v
      rw [D.dnSuccessor_selected_iff e f he hf hfe heq hb hns hlen hgap]
      unfold neutralExchangeRelation
      dsimp only
      rw [← epar, ← fpar, ← emain, ← fmain, B.main_zero, B.main_last, ← et, ← fh] }
  refine ⟨D', ⟨C⟩, ?_, C.preserves_acyclic ha, C.strictRank_lt ha⟩
  rw [D.dnSuccessor_area e f he hf hfe heq hb hns hlen hgap, eh, fh, ← D.residue_succ]

end Diagram
end VerticalStripLLT.Circular
