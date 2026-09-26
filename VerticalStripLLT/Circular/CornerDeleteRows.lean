import VerticalStripLLT.Circular.CornerBoundary

/-! Exact strict-row and east-gap changes when deleting a strict corner. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

variable {n : ℕ} (D : Diagram n)

theorem deleteStrictCorner_strictAt_iff (e : Edge D.area) (he : e ∈ D.strict) (z : ℤ) :
    (D.deleteCorner e (D.strict_corner e he)).strictAt z ↔
      D.strictAt z ∧ D.residue z ≠ e.head := by
  constructor
  · rintro ⟨f, hf, hh⟩
    have hf' := (D.mem_deleteCorner_strict e (D.strict_corner e he) f).mp hf
    refine ⟨⟨D.cornerIncl e (D.strict_corner e he) f, hf', hh⟩, ?_⟩
    intro hz
    exact D.cornerIncl_ne e (D.strict_corner e he) f
      (D.strict_edge_eq_of_head_eq hf' he (hh.trans hz))
  · rintro ⟨⟨f, hf, hh⟩, hz⟩
    have hfe : f ≠ e := by
      intro h
      exact hz (hh.symm.trans (congrArg Edge.head h))
    refine ⟨D.cornerRestrict e (D.strict_corner e he) f hfe, ?_, hh⟩
    exact (D.mem_deleteCorner_strict e (D.strict_corner e he) _).mpr hf

/-- Deleting a strict corner only increases the east gap of the preceding row. -/
theorem deleteStrictCorner_eastGap (e : Edge D.area) (he : e ∈ D.strict) (z : ℤ) :
    (D.deleteCorner e (D.strict_corner e he)).eastGap z =
      D.eastGap z + if D.residue (z + 1) = e.head then 1 else 0 := by
  classical
  unfold eastGap
  rw [D.deleteCorner_boundary, D.deleteCorner_boundary,
    D.deleteStrictCorner_strictAt_iff e he z]
  by_cases hz : D.residue z = e.head
  · have hs : D.strictAt z := ⟨e, he, hz.symm⟩
    simp [hz, hs]
    ring
  · simp [hz]
    ring

end VerticalStripLLT.Circular.Diagram
