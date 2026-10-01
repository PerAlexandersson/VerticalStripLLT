import VerticalStripLLT.Components.DiagramProof.InducedCornerFamily

/-! Deleting the first vertex loses its corner and introduces no new corner. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k : ℕ} {D : Diagram (k + 2)}

theorem mem_range_succOrderEmb_iff (v : Fin (k + 2)) :
    v ∈ Set.range (Fin.succOrderEmb (k + 1)) ↔ v ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact Fin.succ_ne_zero u
  · intro hv
    obtain ⟨u, hu⟩ := Fin.eq_succ_of_ne_zero hv
    exact ⟨u, hu.symm⟩

private theorem corner_eq_of_same_tail (hD : Forward D) {f g : Edge D.area}
    (hf : IsCorner f) (hg : IsCorner g) (ht : f.tail = g.tail) : f = g := by
  apply D.endpointEmbedding.injective
  apply Prod.ext ht
  exact le_antisymm (((isCorner_iff_extremal hD g).mp hg).2 f ht)
    (((isCorner_iff_extremal hD f).mp hf).2 g ht.symm)

/-- After removing zero, the part of its corner lies inside the corner starting at one. -/
theorem inducedEdge_isCorner_iff_initialVertex (hD : Forward D)
    (f g : Edge D.area) (hf : IsCorner f) (hg : IsCorner g)
    (hft : f.tail = 0) (hgt : g.tail = 1) (hfg : f.head < g.head)
    (e : Edge (inducedDiagram hD (Fin.succOrderEmb (k + 1))).area) :
    IsCorner (inducedEdge hD (Fin.succOrderEmb (k + 1)) e) ↔ IsCorner e := by
  constructor
  · exact isCorner_of_inducedEdge_isCorner hD _ e
  · intro he
    let ι := Fin.succOrderEmb (k + 1)
    let p := inducedEdge hD ι e
    have hpt : p.tail ≠ 0 := by
      change (inducedEdge hD ι e).tail ≠ 0
      rw [inducedEdge_tail]
      simpa only [ι, Fin.coe_succOrderEmb] using Fin.succ_ne_zero e.tail
    obtain ⟨h, hh, htp, hph⟩ := exists_corner_containing hD p
    have hex : ∃ q : Edge D.area,
        IsCorner q ∧ q.tail ≠ 0 ∧ q.tail ≤ p.tail ∧ p.head ≤ q.head := by
      by_cases hzero : h.tail = 0
      · have hhf : h = f := corner_eq_of_same_tail hD hh hf (hzero.trans hft.symm)
        refine ⟨g, hg, ?_, ?_, ?_⟩
        · rw [hgt]
          exact one_ne_zero
        · rw [hgt]
          change 1 ≤ p.tail.val
          exact Fin.pos_iff_ne_zero.mpr hpt
        · rw [hhf] at hph
          exact hph.trans hfg.le
      · exact ⟨h, hh, hzero, htp, hph⟩
    obtain ⟨q, hq, hqt, hqp, hpq⟩ := hex
    have hqh : q.head ≠ 0 := ne_of_gt ((Fin.pos_iff_ne_zero.mpr hqt).trans (hD q))
    obtain ⟨u, hu⟩ := (mem_range_succOrderEmb_iff q.tail).mpr hqt
    obtain ⟨v, hv⟩ := (mem_range_succOrderEmb_iff q.head).mpr hqh
    obtain ⟨b, hb⟩ := (mem_range_inducedEdge_iff hD ι q).mpr ⟨u, v, hu, hv⟩
    have hbe : b = e := (isCorner_iff_maximal (inducedDiagram_forward hD ι) e).mp he b
      (ι.le_iff_le.mp (by simpa only [p, ← hb, inducedEdge_tail] using hqp))
      (ι.le_iff_le.mp (by simpa only [p, ← hb, inducedEdge_head] using hpq))
    simpa only [← hb, hbe] using hq

/-- The induced retained family is exactly the maximal-corner family of the core. -/
theorem induced_allCorners_initialVertex (hD : Forward D)
    (f g : Edge D.area) (hf : IsCorner f) (hg : IsCorner g)
    (hft : f.tail = 0) (hgt : g.tail = 1) (hfg : f.head < g.head) :
    (allCorners D).induced hD (Fin.succOrderEmb (k + 1)) =
      allCorners (inducedDiagram hD (Fin.succOrderEmb (k + 1))) := by
  apply CornerFamily.ext_edges
  ext e
  rw [CornerFamily.mem_induced_edges]
  change (inducedEdge hD (Fin.succOrderEmb (k + 1)) e ∈ Finset.univ.filter IsCorner) ↔
    e ∈ Finset.univ.filter IsCorner
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact inducedEdge_isCorner_iff_initialVertex hD f g hf hg hft hgt hfg e

end

end VerticalStripLLT.Circular.DiagramProof
