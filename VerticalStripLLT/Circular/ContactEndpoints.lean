import VerticalStripLLT.Circular.BounceSearch
import VerticalStripLLT.Circular.FirstBounceStrictSwap

/-! Free endpoints of the parallel path of a full DN bounce. -/

namespace VerticalStripLLT.Circular
namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem not_selected_to_of_not_strictAt {x : ℤ} (hx : ¬ D.strictAt x) (v : Fin n) :
    ¬ D.edgeData.selected ∅ v (D.residue x) := by
  rintro ⟨e, he, _, hh⟩
  exact hx ⟨e, by simpa [Diagram.edgeData] using he, hh⟩

theorem EligibleDE.boundary_gap {t : ℤ} (h : D.EligibleDE t) :
    D.boundary t + 2 ≤ D.boundary (t + 1) := by
  have hg := h.2.2
  simp only [eastGap] at hg
  simp only [h.1, ↓reduceIte] at hg
  lia

theorem EligibleDE.boundary_avoids {t : ℤ} (h : D.EligibleDE t) (w k : ℤ) :
    D.boundary w ≠ D.boundary t + 1 + (n : ℤ) * k := by
  intro hw
  have hg := D.no_boundary_gap t (D.boundary t) rfl (h.boundary_gap D)
  apply hg (w + (n : ℤ) * (-k))
  rw [D.boundary_add_period, hw]
  ring

theorem EligibleDE.parallel_end_free {t : ℤ} (h : D.EligibleDE t) (v : Fin n) :
    ¬ D.edgeData.selected ∅ (D.residue (D.boundary t + 1)) v := by
  rintro ⟨e, he, ht, _⟩
  have hs : e ∈ D.strict := by simpa [Diagram.edgeData] using he
  have hm := (D.residue_eq_iff_mod_sub_zero).mp
    ((D.strictEdge_tail_boundary hs).symm.trans ht)
  have hd := Int.mul_ediv_add_emod
    (D.boundary (e.head.val : ℤ) - (D.boundary t + 1)) (n : ℤ)
  rw [hm] at hd
  apply h.boundary_avoids D (e.head.val : ℤ)
    ((D.boundary (e.head.val : ℤ) - (D.boundary t + 1)) / (n : ℤ))
  lia

end Diagram
end VerticalStripLLT.Circular
