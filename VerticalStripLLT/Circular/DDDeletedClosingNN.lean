import VerticalStripLLT.Circular.DDClosingNN
import VerticalStripLLT.Circular.EligibleCornerMoves
import VerticalStripLLT.Circular.OneBounceDNData

/-! The deleted side of the concrete NN closing triple. -/

namespace VerticalStripLLT.Circular.Diagram.DDLocalData

open scoped Classical

variable {n : ℕ} {D : Diagram n} {t : ℤ} (B : D.DDLocalData t)

noncomputable def deletedShortened (hc : B.deleted.EligibleDE (D.boundary t)) : Diagram n :=
  B.deleted.shortenEligible (D.boundary t) hc

include B in
theorem contact_ne_parallel :
    D.residue (D.boundary t) ≠ D.residue (D.boundary t + 1) := by
  rw [← B.eh, ← B.gh]
  intro h
  exact B.heg (D.strict_edge_eq_of_head_eq B.he B.hg h)

include B in
theorem root_ne_contact : D.residue t ≠ D.residue (D.boundary t) := by
  rw [← B.fh, ← B.eh]
  intro h
  exact B.hfe (D.strict_edge_eq_of_head_eq B.hf B.he h)

include B in
theorem root_ne_parallel : D.residue t ≠ D.residue (D.boundary t + 1) := by
  rw [← B.fh, ← B.gh]
  intro h
  exact B.hfg (D.strict_edge_eq_of_head_eq B.hf B.hg h)

theorem deletedShortened_area (hc : B.deleted.EligibleDE (D.boundary t)) :
    (B.deletedShortened hc).area.area = Function.update
      (Function.update D.area.area (D.residue (D.boundary t + 1))
        (D.area.area (D.residue (D.boundary t + 1)) - 1))
      (D.residue (D.boundary t)) (D.area.area (D.residue (D.boundary t)) - 1) := by
  rw [deletedShortened, shortenEligible_area]
  change Function.update (Function.update D.area.area B.g.head
      (D.area.area B.g.head - 1)) (D.residue (D.boundary t))
    (Function.update D.area.area B.g.head (D.area.area B.g.head - 1)
      (D.residue (D.boundary t)) - 1) = _
  rw [B.gh, Function.update_of_ne B.contact_ne_parallel]

theorem deletedShortened_strictAt_iff (hc : B.deleted.EligibleDE (D.boundary t)) (z : ℤ) :
    (B.deletedShortened hc).strictAt z ↔
      D.strictAt z ∧ D.residue z ≠ D.residue (D.boundary t + 1) := by
  rw [deletedShortened, shortenEligible_strictAt_iff]
  change (D.deleteCorner B.g (D.strict_corner B.g B.hg)).strictAt z ↔ _
  rw [D.deleteStrictCorner_strictAt_iff B.g B.hg, B.gh]

theorem deletedShortened_root_eligible (ht : D.EligibleDE t)
    (hc : B.deleted.EligibleDE (D.boundary t)) : (B.deletedShortened hc).EligibleDE t := by
  have hroot : B.deleted.EligibleDE t :=
    D.deleteStrictCorner_preserves_eligible ht B.g B.hg (by rw [B.gh]; exact B.root_ne_parallel)
  exact B.deleted.shortenEligible_preserves_eligible hc hroot B.root_ne_contact

theorem deletedShortened_root_boundary (hc : B.deleted.EligibleDE (D.boundary t)) :
    (B.deletedShortened hc).boundary t = D.boundary t := by
  change t - ((B.deletedShortened hc).area.area (D.residue t) : ℤ) = D.boundary t
  rw [B.deletedShortened_area, Function.update_of_ne B.root_ne_contact,
    Function.update_of_ne B.root_ne_parallel]
  rfl

theorem deletedShortened_contact_strict (hc : B.deleted.EligibleDE (D.boundary t)) :
    (B.deletedShortened hc).strictAt (D.boundary t) :=
  (B.deletedShortened_strictAt_iff hc _).mpr ⟨⟨B.e, B.he, B.eh⟩, B.contact_ne_parallel⟩

theorem deletedShortened_parallel_nonstrict (hc : B.deleted.EligibleDE (D.boundary t)) :
    ¬ (B.deletedShortened hc).strictAt (D.boundary t + 1) := by
  rw [B.deletedShortened_strictAt_iff]
  exact fun h => h.2 rfl

theorem deletedShortened_contact_gap (hc : B.deleted.EligibleDE (D.boundary t)) :
    (B.deletedShortened hc).eastGap (D.boundary t) = 0 := by
  unfold eastGap
  rw [ite_eq_left (B.deletedShortened_contact_strict hc)]
  change (D.boundary t + 1 -
      ((B.deletedShortened hc).area.area (D.residue (D.boundary t + 1)) : ℤ)) -
    (D.boundary t - ((B.deletedShortened hc).area.area (D.residue (D.boundary t)) : ℤ)) - 1 = 0
  rw [B.deletedShortened_area, Function.update_of_ne B.contact_ne_parallel.symm,
    Function.update_self, Function.update_self]
  have hs : D.area.area (D.residue (D.boundary t + 1)) =
      D.area.area (D.residue (D.boundary t)) := by
    rw [D.residue_succ, ← B.eh]
    exact B.sameArea
  rw [hs]
  ring

theorem deletedShortened_oneBounce (hc : B.deleted.EligibleDE (D.boundary t)) :
    ReverseBounceN (B.deletedShortened hc) t (D.boundary t) 0 := by
  apply (ReverseBounceN.zero_iff _).mpr
  exact ⟨(B.deletedShortened_root_boundary hc).symm,
    B.deletedShortened_contact_gap hc, fun h => B.deletedShortened_parallel_nonstrict hc h.2⟩

noncomputable def closingDN (ht : D.EligibleDE t)
    (hc : B.deleted.EligibleDE (D.boundary t)) : (B.deletedShortened hc).OneBounceDNData t :=
  Classical.choice (exists_oneBounceDNData (B.deletedShortened_root_eligible ht hc)
    (B.deletedShortened_oneBounce hc) (B.deletedShortened_contact_strict hc)
    (B.deletedShortened_parallel_nonstrict hc))

theorem closingDN_first_head (ht : D.EligibleDE t)
    (hc : B.deleted.EligibleDE (D.boundary t)) :
    (B.closingDN ht hc).e.head = D.residue (D.boundary t) := by
  rw [(B.closingDN ht hc).eh, B.deletedShortened_root_boundary]
  rfl

theorem closingDN_last_head (ht : D.EligibleDE t)
    (hc : B.deleted.EligibleDE (D.boundary t)) :
    (B.closingDN ht hc).f.head = D.residue t := (B.closingDN ht hc).fh

theorem closingDN_target_area (ht : D.EligibleDE t)
    (hc : B.deleted.EligibleDE (D.boundary t)) :
    (B.closingDN ht hc).target.area.area = Function.update
      (Function.update D.area.area (D.residue (D.boundary t))
        (D.area.area (D.residue (D.boundary t)) - 1))
      (D.residue t) (D.area.area (D.residue t) - 1) := by
  have hn : (B.deletedShortened hc).area.next (B.closingDN ht hc).e.head =
      D.residue (D.boundary t + 1) := by
    rw [B.closingDN_first_head]
    exact (D.residue_succ _).symm
  rw [(B.closingDN ht hc).target_area, hn, B.closingDN_first_head,
    B.closingDN_last_head, B.deletedShortened_area]
  have hpos : 1 ≤ D.area.area (D.residue (D.boundary t)) :=
    D.strictAt_area_pos ⟨B.e, B.he, B.eh⟩
  have hsame : D.area.area (D.residue (D.boundary t + 1)) =
      D.area.area (D.residue (D.boundary t)) := by
    rw [D.residue_succ, ← B.eh]
    exact B.sameArea
  rw [Function.update_self, Nat.sub_add_cancel hpos,
    Function.update_of_ne B.root_ne_contact, Function.update_of_ne B.root_ne_parallel]
  funext v
  by_cases hvt : v = D.residue t
  · subst v
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hvt, Function.update_of_ne hvt]
    by_cases hvq : v = D.residue (D.boundary t + 1)
    · subst v
      rw [Function.update_self, Function.update_of_ne B.contact_ne_parallel.symm, hsame]
    · rw [Function.update_of_ne hvq]
      by_cases hvc : v = D.residue (D.boundary t)
      · subst v
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hvc, Function.update_of_ne hvq,
          Function.update_of_ne hvc]

theorem closingDN_target_strictAt_iff (ht : D.EligibleDE t)
    (hc : B.deleted.EligibleDE (D.boundary t)) (z : ℤ) :
    (B.closingDN ht hc).target.strictAt z ↔
      D.strictAt z ∧ D.residue z ≠ D.residue (D.boundary t) := by
  have hn : (B.deletedShortened hc).area.next (B.closingDN ht hc).e.head =
      D.residue (D.boundary t + 1) := by
    rw [B.closingDN_first_head]
    exact (D.residue_succ _).symm
  rw [(B.closingDN ht hc).target_strictAt_iff, B.deletedShortened_strictAt_iff,
    hn, B.closingDN_first_head]
  change ((D.strictAt z ∧ D.residue z ≠ D.residue (D.boundary t + 1)) ∧
    D.residue z ≠ D.residue (D.boundary t)) ∨
    D.residue z = D.residue (D.boundary t + 1) ↔ _
  constructor
  · rintro (⟨⟨hs, _⟩, hz⟩ | hz)
    · exact ⟨hs, hz⟩
    · exact ⟨⟨B.g, B.hg, B.gh.trans hz.symm⟩,
        fun h => B.contact_ne_parallel (h.symm.trans hz)⟩
  · rintro ⟨hs, hz⟩
    by_cases hq : D.residue z = D.residue (D.boundary t + 1)
    · exact Or.inr hq
    · exact Or.inl ⟨⟨hs, hq⟩, hz⟩

/-- The direct DN move on the deleted shortening closes the original corner triple. -/
theorem closingDN_target_eq_deleteCorner (ht : D.EligibleDE t)
    (hc : B.deleted.EligibleDE (D.boundary t))
    (e : Edge (D.shortenEligible t ht).area)
    (he : e ∈ (D.shortenEligible t ht).strict)
    (hh : e.head = D.residue (D.boundary t)) :
    (B.closingDN ht hc).target =
      (D.shortenEligible t ht).deleteCorner e ((D.shortenEligible t ht).strict_corner e he) := by
  apply ext_of_area_eq_of_strictAt
  · rw [B.closingDN_target_area]
    change _ = Function.update (D.shortenEligible t ht).area.area e.head
      ((D.shortenEligible t ht).area.area e.head - 1)
    rw [D.shortenEligible_area, hh, Function.update_of_ne B.root_ne_contact.symm]
    funext v
    by_cases hvt : v = D.residue t
    · subst v
      rw [Function.update_self, Function.update_of_ne B.root_ne_contact,
        Function.update_self]
    · rw [Function.update_of_ne hvt]
      by_cases hvc : v = D.residue (D.boundary t)
      · subst v
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hvc, Function.update_of_ne hvc,
          Function.update_of_ne hvt]
  · intro z
    rw [B.closingDN_target_strictAt_iff,
      (D.shortenEligible t ht).deleteStrictCorner_strictAt_iff e he,
      D.shortenEligible_strictAt_iff]
    change _ ↔ D.strictAt z ∧ D.residue z ≠ e.head
    rw [hh]

end VerticalStripLLT.Circular.Diagram.DDLocalData
