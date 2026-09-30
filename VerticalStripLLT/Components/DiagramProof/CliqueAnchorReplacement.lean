import VerticalStripLLT.Components.DiagramProof.TerminalClique

/-! Anchor preservation when the earlier rows are fixed during a last-clique replacement. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {k n : ℕ} {D : Diagram n} (F : CornerFamily D) (hD : Forward D)

/-- Every natural edge starting after the last corner tail is good. -/
theorem goodEdge_of_last_tail_lt (g : Edge D.area) (hlast : ∀ v : Fin n, v ≤ g.head)
    {f : Edge D.area} (ht : g.tail < f.tail) : F.GoodEdge hD f := by
  right
  rw [F.terminal_eq_of_last_corner hD g hlast ht,
    F.terminal_eq_of_last_corner hD g hlast (ht.trans (hD f))]
  exact hD f

/-- Fixing the rows up to the last corner tail preserves the anchor property. -/
theorem anchor_of_rows_le_last_tail (g : Edge D.area)
    (hlast : ∀ v : Fin n, v ≤ g.head) (θ η : Orientation D) (hθ : F.Anchor hD θ)
    (hrows : ∀ u v, u ≤ g.tail →
      (D.edgeData.selected η.val u v ↔ D.edgeData.selected θ.val u v)) :
    F.Anchor hD η := by
  constructor
  · intro f hf
    apply (mem_fullSelection_iff_selected η f).mpr
    apply (hrows f.tail f.head (F.corner_tail_le_of_head_le hD hf (hlast f.head))).mpr
    exact (mem_fullSelection_iff_selected θ f).mp (hθ.1 hf)
  · intro f hf
    by_cases ht : f.tail ≤ g.tail
    · apply hθ.2 f
      exact (mem_fullSelection_iff_selected θ f).mpr
        ((hrows f.tail f.head ht).mp ((mem_fullSelection_iff_selected η f).mp hf))
    · exact F.goodEdge_of_last_tail_lt hD g hlast (lt_of_not_ge ht)

/-- Replacing a block strictly after the last corner tail preserves every anchor. -/
theorem anchor_of_last_clique_block_replacement (g : Edge D.area)
    (hlast : ∀ v : Fin n, v ≤ g.head) (ι : Fin (k + 1) ↪o Fin n)
    (htail : ∀ i, g.tail < ι i) (θ η : Orientation D) (hθ : F.Anchor hD θ)
    (houtside : ∀ u v, (¬ ∃ a b, ι a = u ∧ ι b = v) →
      (D.edgeData.selected η.val u v ↔ D.edgeData.selected θ.val u v)) :
    F.Anchor hD η := by
  apply F.anchor_of_rows_le_last_tail hD g hlast θ η hθ
  intro u v hu
  apply houtside u v
  rintro ⟨a, _, ha, _⟩
  exact (not_le_of_gt (htail a)) (ha.symm ▸ hu)

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
