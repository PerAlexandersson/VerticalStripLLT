import VerticalStripLLT.Circular.CornerDeleteOrientation
import VerticalStripLLT.Circular.NaturalPairSwap

/-! Endpoint pairs after deleting a strict corner. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

theorem deleteCorner_naturalPairs (e : Edge D.area) (he : IsCorner e) :
    (D.deleteCorner e he).naturalPairs = D.naturalPairs.erase (e.tail, e.head) := by
  ext x
  rw [mem_naturalPairs_iff, Finset.mem_erase, D.mem_naturalPairs_iff]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨?_, ⟨D.cornerIncl e he f, hf⟩⟩
    intro h
    exact D.cornerIncl_ne e he f (D.endpointEmbedding.injective (hf.trans h))
  · rintro ⟨hne, f, hf⟩
    have hfe : f ≠ e := fun h => hne (hf.symm.trans (congrArg D.endpointEmbedding h))
    exact ⟨D.cornerRestrict e he f hfe, hf⟩

theorem deleteCorner_pairGraph_strictEdges (e : Edge D.area) (he : IsCorner e) :
    (D.deleteCorner e he).pairGraph.strictEdges =
      D.pairGraph.strictEdges.erase (e.tail, e.head) := by
  ext x
  rw [mem_pairGraph_strict_iff, Finset.mem_erase, D.mem_pairGraph_strict_iff]
  constructor
  · rintro ⟨f, hf, hpair⟩
    refine ⟨?_, ⟨D.cornerIncl e he f, (D.mem_deleteCorner_strict e he f).mp hf, hpair⟩⟩
    intro h
    exact D.cornerIncl_ne e he f (D.endpointEmbedding.injective (hpair.trans h))
  · rintro ⟨hne, f, hf, hpair⟩
    have hfe : f ≠ e := fun h => hne (hpair.symm.trans (congrArg D.endpointEmbedding h))
    exact ⟨D.cornerRestrict e he f hfe,
      (D.mem_deleteCorner_strict e he _).mpr hf, hpair⟩

theorem deleteStrictCorner_pairGraph_normalEdges (e : Edge D.area) (he : e ∈ D.strict) :
    (D.deleteCorner e (D.strict_corner e he)).pairGraph.normalEdges =
      D.pairGraph.normalEdges := by
  rw [normalPairs_eq_sdiff, D.normalPairs_eq_sdiff, D.deleteCorner_naturalPairs,
    D.deleteCorner_pairGraph_strictEdges]
  have hs : (e.tail, e.head) ∈ D.pairGraph.strictEdges :=
    (D.mem_pairGraph_strict_iff _).mpr ⟨e, he, rfl⟩
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_erase]
  by_cases hx : x = (e.tail, e.head)
  · subst x; simp [hs]
  · simp [hx]

end VerticalStripLLT.Circular.Diagram
