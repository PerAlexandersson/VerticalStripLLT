import VerticalStripLLT.Circular.DNRealization
import VerticalStripLLT.Circular.DNStrictRows
import VerticalStripLLT.Circular.DiagramExt

set_option backward.isDefEq.respectTransparency false

/-! The concrete DN target of a bounce, described by its area and strict rows. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ}

/-- `T` has exactly the rows of the DN move for the root `t` and terminal row `x`:
row `x + 1` is raised to `area x + 1`, row `t` is lowered by one, the strict row at
`x` moves to `x + 1`, and all other strict rows are unchanged. -/
def IsDNTarget (D : Diagram n) (t x : ℤ) (T : Diagram n) : Prop :=
  T.area.area = Function.update
      (Function.update D.area.area (D.residue (x + 1))
        (D.area.area (D.residue x) + 1)) (D.residue t)
          (D.area.area (D.residue t) - 1) ∧
    ∀ z : ℤ, T.strictAt z ↔ (D.strictAt z ∧ D.residue z ≠ D.residue x) ∨
      D.residue z = D.residue (x + 1)

theorem strictAt_congr_residue (D : Diagram n) {z w : ℤ} (h : D.residue z = D.residue w) :
    D.strictAt z ↔ D.strictAt w := by
  unfold strictAt
  rw [h]

theorem residue_ne_of_strictAt (D : Diagram n) {z w : ℤ} (hz : D.strictAt z)
    (hw : ¬ D.strictAt w) : D.residue z ≠ D.residue w :=
  fun h => hw ((D.strictAt_congr_residue h).mp hz)

theorem IsDNTarget.eq {D T T' : Diagram n} {t x : ℤ} (h : IsDNTarget D t x T)
    (h' : IsDNTarget D t x T') : T = T' :=
  ext_of_area_eq_of_strictAt (h.1.trans h'.1.symm) (fun z => (h.2 z).trans (h'.2 z).symm)

theorem dnSuccessor_isDNTarget (D : Diagram n) {t x : ℤ}
    (e f : Edge D.area) (he : e ∈ D.strict) (hf : f ∈ D.strict) (hfe : f ≠ e)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
    (hlen : 2 ≤ f.length.val)
    (hgap : D.area.area (D.area.next f.head) < D.area.area f.head)
    (eh : e.head = D.residue x) (fh : f.head = D.residue t) :
    IsDNTarget D t x (D.dnSuccessor e f he hf hfe heq hb hns hlen hgap) := by
  refine ⟨?_, fun z => ?_⟩
  · rw [D.dnSuccessor_area e f he hf hfe heq hb hns hlen hgap, eh, fh, ← D.residue_succ]
  · rw [D.dnSuccessor_strictAt_iff e f he hf hfe heq hb hns hlen hgap, eh, ← D.residue_succ]

/-- The concrete edges of the DN move for an eligible reverse bounce, together with the
full neutral-bounce witness of the resulting successor. -/
theorem exists_dn_data (D : Diagram n) {t x : ℤ}
    (ha : D.edgeData.Admissible ∅) (ht : D.EligibleDE t)
    (h : ReverseBounce D t x) (hx : D.strictAt x) (hx1 : ¬ D.strictAt (x + 1)) :
    ∃ (e f : Edge D.area) (he : e ∈ D.strict) (hf : f ∈ D.strict) (hfe : f ≠ e)
      (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
      (hb : D.area.area e.head + 1 < n)
      (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
      (hlen : 2 ≤ f.length.val)
      (hgap : D.area.area (D.area.next f.head) < D.area.area f.head),
      e.head = D.residue x ∧ f.head = D.residue t ∧
        Nonempty (FullNeutralBounce D (D.dnSuccessor e f he hf hfe heq hb hns hlen hgap)) := by
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
  exact ⟨e, f, he, hf, hfe, heq, hb, hns, hlen, hgap, eh, fh, ⟨C⟩⟩

end VerticalStripLLT.Circular.Diagram
