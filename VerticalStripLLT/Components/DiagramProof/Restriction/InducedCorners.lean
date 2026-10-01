import VerticalStripLLT.Components.DiagramProof.Restriction.InducedDiagram
import VerticalStripLLT.Components.DiagramProof.Corners.CornerMaximality
import VerticalStripLLT.Components.DiagramProof.Foundation.MaximalIntervals

/-! Corners and maximal natural intervals under increasing restriction. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

/-- A corner is precisely a natural interval contained in no larger natural interval. -/
theorem isCorner_iff_maximal (hD : Forward D) (e : Edge D.area) :
    IsCorner e ↔ ∀ f : Edge D.area, f.tail ≤ e.tail → e.head ≤ f.head → f = e := by
  classical
  constructor
  · intro he f ht hh
    have heF : e ∈ (allCorners D).edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
    have htail : f.tail = e.tail := le_antisymm ht
      ((allCorners D).corner_tail_le_of_head_le hD heF hh)
    have hhead : f.head = e.head := le_antisymm
      ((allCorners D).head_le_of_same_tail hD heF htail) hh
    exact D.endpointEmbedding.injective (Prod.ext htail hhead)
  · intro hmax
    apply (isCorner_iff_extremal hD e).mpr
    constructor
    · intro f hh
      rcases le_total e.tail f.tail with ht | ht
      · exact ht
      · have hfe := hmax f ht hh.symm.le
        exact (congrArg Edge.tail hfe).symm.le
    · intro f ht
      rcases le_total f.head e.head with hh | hh
      · exact hh
      · have hfe := hmax f ht.le hh
        exact (congrArg Edge.head hfe).le

/-- Every natural edge is contained in a maximal natural corner. -/
theorem exists_corner_containing (hD : Forward D) (e : Edge D.area) :
    ∃ f : Edge D.area, IsCorner f ∧ f.tail ≤ e.tail ∧ e.head ≤ f.head := by
  let R : Fin n → Fin n → Prop := fun u v => ∃ f : Edge D.area, f.tail = u ∧ f.head = v
  have hforward : ∀ ⦃u v⦄, R u v → u < v := by
    rintro u v ⟨f, rfl, rfl⟩
    exact hD f
  obtain ⟨a, b, ⟨f, ht, hh⟩, ha, hb, hmax⟩ :=
    exists_maximal_interval hforward (show R e.tail e.head from ⟨e, rfl, rfl⟩)
  refine ⟨f, (isCorner_iff_maximal hD f).mpr ?_, ht.symm ▸ ha, hh.symm ▸ hb⟩
  intro g hgt hgh
  obtain ⟨hga, hgb⟩ := hmax g.tail g.head ⟨g, rfl, rfl⟩
    (hgt.trans ht.le) (hh.symm.le.trans hgh)
  exact D.endpointEmbedding.injective (Prod.ext (hga.trans ht.symm) (hgb.trans hh.symm))

variable {k : ℕ} (hD : Forward D) (ι : Fin (k + 1) ↪o Fin n)

/-- An ambient corner whose endpoints survive remains a corner in the induced diagram. -/
theorem isCorner_of_inducedEdge_isCorner (e : Edge (inducedUndecorated hD ι).area)
    (he : IsCorner (inducedEdge hD ι e)) : IsCorner e := by
  apply (isCorner_iff_extremal (inducedUndecorated_forward hD ι) e).mpr
  have hext := (isCorner_iff_extremal hD (inducedEdge hD ι e)).mp he
  constructor
  · intro f hh
    apply ι.le_iff_le.mp
    simpa only [inducedEdge_tail] using hext.1 (inducedEdge hD ι f)
      (by simp only [inducedEdge_head, hh])
  · intro f ht
    apply ι.le_iff_le.mp
    simpa only [inducedEdge_head] using hext.2 (inducedEdge hD ι f)
      (by simp only [inducedEdge_tail, ht])

/-- If every ambient corner survives, restriction introduces no new maximal corners. -/
theorem inducedEdge_isCorner_iff
    (hcorners : ∀ f : Edge D.area, IsCorner f →
      ∃ u v, ι u = f.tail ∧ ι v = f.head)
    (e : Edge (inducedUndecorated hD ι).area) :
    IsCorner (inducedEdge hD ι e) ↔ IsCorner e := by
  constructor
  · exact isCorner_of_inducedEdge_isCorner hD ι e
  · intro he
    obtain ⟨f, hf, ht, hh⟩ := exists_corner_containing hD (inducedEdge hD ι e)
    obtain ⟨g, hg⟩ := (mem_range_inducedEdge_iff hD ι f).mpr (hcorners f hf)
    have hge : g = e := (isCorner_iff_maximal (inducedUndecorated_forward hD ι) e).mp he g
      (ι.le_iff_le.mp (by simpa only [← hg, inducedEdge_tail] using ht))
      (ι.le_iff_le.mp (by simpa only [← hg, inducedEdge_head] using hh))
    simpa only [← hg, hge] using hf

end VerticalStripLLT.Circular.DiagramProof
