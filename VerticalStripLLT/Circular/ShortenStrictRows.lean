import VerticalStripLLT.Circular.ShortenStrict
import VerticalStripLLT.Circular.CornerDeleteRows

/-! Strict rows and lifted boundaries after shortening a strict corner. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

theorem shortenStrict_strictAt_iff (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head) (z : ℤ) :
    (D.shortenStrict e he hlen hgap).strictAt z ↔ D.strictAt z := by
  constructor
  · rintro ⟨f, hf, hhead⟩
    rcases (D.shortenStrict_strict_mem e he hlen hgap f).mp hf with hnew | hold
    · subst f
      refine ⟨e, he, ?_⟩
      exact (D.shortenedEdge_head e he hlen).symm.trans hhead
    · exact ⟨D.cornerIncl e (D.strict_corner e he) f, hold, hhead⟩
  · intro hs
    by_cases hz : D.residue z = e.head
    · refine ⟨D.shortenedEdge e he hlen, ?_, ?_⟩
      · exact (D.shortenStrict_strict_mem e he hlen hgap _).mpr (Or.inl rfl)
      · exact (D.shortenedEdge_head e he hlen).trans hz.symm
    · obtain ⟨f, hf, hhead⟩ :=
        (D.deleteStrictCorner_strictAt_iff e he z).mpr ⟨hs, hz⟩
      exact ⟨f, (D.shortenStrict_strict_mem e he hlen hgap f).mpr (Or.inr
        ((D.mem_deleteCorner_strict e (D.strict_corner e he) f).mp hf)), hhead⟩

theorem shortenStrict_boundary (e : Edge D.area) (he : e ∈ D.strict)
    (hlen : 2 ≤ e.length.val)
    (hgap : D.area.area (D.area.next e.head) < D.area.area e.head) (z : ℤ) :
    (D.shortenStrict e he hlen hgap).boundary z =
      D.boundary z + if D.residue z = e.head then 1 else 0 := by
  change (D.deleteCorner e (D.strict_corner e he)).boundary z = _
  exact D.deleteCorner_boundary e (D.strict_corner e he) z

end VerticalStripLLT.Circular.Diagram
