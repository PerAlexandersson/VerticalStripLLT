import VerticalStripLLT.Components.DiagramProof.LastClique.CliqueAnchorReplacement
import VerticalStripLLT.Components.DiagramProof.Preparation.CopyPaths

/-! The two natural copies created by crossing retained corners. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hD : Forward D)

/-- Crossing retained corners `f` and `g` produce linked natural copies from `f.tail` to
`g.tail` and from `f.head` to `g.head`; the first is good. -/
theorem exists_crossing_copies
    (f g : Edge D.area) (hf : f ∈ F.edges) (hg : g ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ g.head)
    (hcross : f.tail < g.tail ∧ g.tail < f.head ∧ f.head < g.head) :
    ∃ p q : Edge D.area,
      p.tail = f.tail ∧ p.head = g.tail ∧
      q.tail = f.head ∧ q.head = g.head ∧
      F.CopyLink p q ∧
      F.terminal hD p.tail < F.terminal hD p.head ∧
      p ∈ F.goodEdges hD := by
  obtain ⟨p, hpt, hph⟩ := exists_edge_of_naturalLift_of_le
    (D.naturalLift_of_tail_lt_head f (hD f)) le_rfl hcross.1 hcross.2.1.le
  obtain ⟨q, hqt, hqh⟩ := exists_edge_of_naturalLift_of_le
    (D.naturalLift_of_tail_lt_head g (hD g)) hcross.2.1.le hcross.2.2 le_rfl
  have hpstep : F.step p.tail q.tail := by
    rw [hpt, hqt]
    exact (F.step_iff _ _).mpr ⟨f, hf, rfl, rfl⟩
  have hqstep : F.step p.head q.head := by
    rw [hph, hqh]
    exact (F.step_iff _ _).mpr ⟨g, hg, rfl, rfl⟩
  have hlink : F.CopyLink p q := by
    refine ⟨hpstep, hqstep, ?_⟩
    rw [hph, hqt]
    exact hcross.2.1
  have hpgood : p ∈ F.goodEdges hD := by
    apply (F.mem_goodEdges hD p).mpr
    right
    rw [hpt, hph, (F.terminal_eq_iff_mem hD f).mpr hf,
      (F.terminal_eq_iff_mem hD g).mpr hg,
      F.terminal_eq_of_last_corner hD g hlast hcross.2.1,
      F.terminal_eq_of_last_corner hD g hlast (hD g)]
    exact hcross.2.2
  refine ⟨p, q, hpt, hph, hqt, hqh, hlink, ?_, hpgood⟩
  rw [hpt, hph]
  rw [(F.terminal_eq_iff_mem hD f).mpr hf,
    (F.terminal_eq_iff_mem hD g).mpr hg,
    F.terminal_eq_of_last_corner hD g hlast hcross.2.1,
    F.terminal_eq_of_last_corner hD g hlast (hD g)]
  exact hcross.2.2

end

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
