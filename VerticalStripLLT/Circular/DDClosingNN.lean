import VerticalStripLLT.Circular.DiagramExt
import VerticalStripLLT.Circular.EligibleShorten
import VerticalStripLLT.Circular.DDResolvedStrict
import VerticalStripLLT.Circular.DDResolvedRows

/-! The raised side of the concrete NN closing triple. -/

namespace VerticalStripLLT.Circular.Diagram.DDLocalData

open scoped Classical

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.DDLocalData t)

theorem resolved_shorten_area (ht : D.EligibleDE t)
    (hr : B.resolved.EligibleDE (D.boundary t + 1)) :
    (B.resolved.shortenEligible (D.boundary t + 1) hr).area.area =
      (D.shortenEligible t ht).area.area := by
  have hqt : D.residue (D.boundary t + 1) ≠ D.residue t := by
    rw [← B.gh, ← B.fh]
    intro h
    exact B.hfg (D.strict_edge_eq_of_head_eq B.hf B.hg h.symm)
  have hsame : D.area.area (D.residue (D.boundary t + 1)) =
      D.area.area (D.residue (D.boundary t)) := by
    rw [D.residue_succ, ← B.eh]
    exact B.sameArea
  rw [shortenEligible_area, shortenEligible_area]
  change Function.update B.resolved.area.area (D.residue (D.boundary t + 1))
      (B.resolved.area.area (D.residue (D.boundary t + 1)) - 1) = _
  rw [B.resolved_area, Function.update_of_ne hqt, Function.update_self]
  rw [Nat.add_sub_cancel, ← hsame]
  funext v
  by_cases hvq : v = D.residue (D.boundary t + 1)
  · subst v
    rw [Function.update_self, Function.update_of_ne hqt]
  · rw [Function.update_of_ne hvq]
    by_cases hvt : v = D.residue t
    · subst v
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hvt, Function.update_of_ne hvq,
        Function.update_of_ne hvt]

/-- Shortening the resolved child's root gives the original shortened target
with precisely the last main DD edge unstricted. -/
theorem resolved_shorten_eq_unstrict (ht : D.EligibleDE t)
    (hr : B.resolved.EligibleDE (D.boundary t + 1)) :
    ∃ (e : Edge (D.shortenEligible t ht).area)
      (he : e ∈ (D.shortenEligible t ht).strict),
      e.head = D.residue (D.boundary t) ∧
      B.resolved.shortenEligible (D.boundary t + 1) hr =
        (D.shortenEligible t ht).unstrict e he := by
  obtain ⟨e, he, hh⟩ := (D.shortenEligible_strictAt_iff t ht (D.boundary t)).mpr
    (show D.strictAt (D.boundary t) from ⟨B.e, B.he, B.eh⟩)
  change e.head = D.residue (D.boundary t) at hh
  refine ⟨e, he, hh, ext_of_area_eq_of_strictAt (B.resolved_shorten_area ht hr) ?_⟩
  intro z
  rw [shortenEligible_strictAt_iff, B.resolved_strictAt_iff,
    unstrict_strictAt_iff, shortenEligible_strictAt_iff]
  change (D.strictAt z ∧ D.residue z ≠ D.residue (D.boundary t)) ↔
    (D.strictAt z ∧ D.residue z ≠ e.head)
  rw [hh]

end VerticalStripLLT.Circular.Diagram.DDLocalData
