import VerticalStripLLT.Circular.OneBounceND
import VerticalStripLLT.Circular.NNElimination
import VerticalStripLLT.Circular.FullDNRecurrences
import VerticalStripLLT.Circular.NeutralExchangeAcyclic
set_option backward.isDefEq.respectTransparency false


/-! Generic row-level facts used by the separated ND reduction: residues of
boundaries, strict selected edges in terms of strict rows, corner edges at a
prescribed row, and the strict rows of corner edits. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ}

theorem ndSep_residue_add_congr (D : Diagram n) {z w : ℤ} (h : D.residue z = D.residue w)
    (c : ℤ) : D.residue (z + c) = D.residue (w + c) := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  have hv := congrArg (fun a : Fin n => (a.val : ℤ)) h
  beta_reduce at hv
  rw [D.residue_coe_val, D.residue_coe_val] at hv ⊢
  rw [Int.add_emod, hv, ← Int.add_emod]

theorem ndSep_residue_boundary_congr (P : Diagram n) {z w : ℤ}
    (h : P.residue z = P.residue w) (c : ℤ) :
    P.residue (P.boundary z + c) = P.residue (P.boundary w + c) := by
  unfold boundary
  rw [h, show z - (P.area.area (P.residue w) : ℤ) + c =
      z + (c - (P.area.area (P.residue w) : ℤ)) by ring,
    show w - (P.area.area (P.residue w) : ℤ) + c =
      w + (c - (P.area.area (P.residue w) : ℤ)) by ring]
  exact P.ndSep_residue_add_congr h _

/-- A strict selected edge into the row `z` is exactly the strict row `z` with tail at its
lifted boundary. -/
theorem ndSep_selected_residue_iff (P : Diagram n) (u : Fin n) (z : ℤ) :
    P.edgeData.selected ∅ u (P.residue z) ↔
      P.strictAt z ∧ u = P.residue (P.boundary z) := by
  constructor
  · rintro ⟨e, he, hu, hv⟩
    have hs : e ∈ P.strict := by simpa [edgeData] using he
    exact ⟨⟨e, hs, hv⟩, hu.symm.trans (P.strictEdge_tail_of_lift hs hv)⟩
  · rintro ⟨hs, rfl⟩
    exact P.selected_of_strictAt hs

/-- The full-height edge at a column of positive area. -/
def ndSepCornerAt (P : Diagram n) (v : Fin n) (hpos : 0 < P.area.area v) : Edge P.area :=
  ⟨(v, ⟨P.area.area v, P.area.bound v⟩), hpos, le_rfl⟩

theorem ndSepCornerAt_head (P : Diagram n) (v : Fin n) (hpos : 0 < P.area.area v) :
    (P.ndSepCornerAt v hpos).head = v := rfl

theorem ndSepCornerAt_isCorner (P : Diagram n) (v : Fin n) (hpos : 0 < P.area.area v)
    (hle : P.area.area (P.area.next v) ≤ P.area.area v) : IsCorner (P.ndSepCornerAt v hpos) :=
  ⟨rfl, hle⟩

theorem ndSepCornerAt_not_mem (P : Diagram n) {z : ℤ} (hpos : 0 < P.area.area (P.residue z))
    (hns : ¬ P.strictAt z) : P.ndSepCornerAt (P.residue z) hpos ∉ P.strict :=
  fun hm => hns ⟨_, hm, rfl⟩

theorem ndSep_strictify_strictAt_iff (P : Diagram n) (e : Edge P.area) (he : IsCorner e)
    (z : ℤ) : (P.strictify e he).strictAt z ↔ P.strictAt z ∨ P.residue z = e.head := by
  constructor
  · rintro ⟨f, hf, hh⟩
    rcases Finset.mem_insert.mp hf with hfe | hf
    · rw [hfe] at hh
      exact Or.inr hh.symm
    · exact Or.inl ⟨f, hf, hh⟩
  · rintro (⟨f, hf, hh⟩ | hh)
    · exact ⟨f, Finset.mem_insert_of_mem hf, hh⟩
    · exact ⟨e, Finset.mem_insert_self _ _, hh.symm⟩

theorem ndSep_deleteCorner_strictAt_iff_of_not_mem (P : Diagram n) (e : Edge P.area)
    (he : IsCorner e) (hns : e ∉ P.strict) (z : ℤ) :
    (P.deleteCorner e he).strictAt z ↔ P.strictAt z := by
  constructor
  · rintro ⟨f, hf, hh⟩
    exact ⟨P.cornerIncl e he f, (P.mem_deleteCorner_strict e he f).mp hf, hh⟩
  · rintro ⟨f, hf, hh⟩
    have hfe : f ≠ e := fun h => hns (h ▸ hf)
    exact ⟨P.cornerRestrict e he f hfe, (P.mem_deleteCorner_strict e he _).mpr hf, hh⟩

theorem ndSep_deleteCorner_area (P : Diagram n) (e : Edge P.area) (he : IsCorner e) :
    (P.deleteCorner e he).area.area =
      Function.update P.area.area e.head (P.area.area e.head - 1) := rfl

/-- Acyclicity passes to a diagram whose strict rows are strict rows of the source with the
same area. -/
theorem ndSep_admissible_of_rows {D P : Diagram n} (ha : D.edgeData.Admissible ∅)
    (h : ∀ z, P.strictAt z → D.strictAt z ∧
      P.area.area (D.residue z) = D.area.area (D.residue z)) :
    P.edgeData.Admissible ∅ := by
  have hsel : ∀ u v, P.edgeData.selected ∅ u v → D.edgeData.selected ∅ u v := by
    intro u v huv
    obtain ⟨z, rfl⟩ : ∃ z : ℤ, D.residue z = v :=
      ⟨v.val, Orientation.residue_intCast_eq v⟩
    have huv' : P.edgeData.selected ∅ u (P.residue z) := huv
    obtain ⟨hs, hu⟩ := (P.ndSep_selected_residue_iff u z).mp huv'
    obtain ⟨hDs, harea⟩ := h z hs
    refine (D.ndSep_selected_residue_iff u z).mpr ⟨hDs, ?_⟩
    rw [hu]
    change D.residue (z - (P.area.area (D.residue z) : ℤ)) = _
    rw [harea]
    rfl
  intro v hv
  exact ha v (Relation.TransGen.mono hsel _ _ hv)

/-- Eligibility transfers when the root row and its strictness are unchanged and the next
row does not grow. -/
theorem ndSep_eligible_transfer {D P : Diagram n} {t : ℤ} (ht : D.EligibleDE t)
    (hs : P.strictAt t ↔ D.strictAt t)
    (hat : P.area.area (D.residue t) = D.area.area (D.residue t))
    (hle : P.area.area (D.residue (t + 1)) ≤ D.area.area (D.residue (t + 1))) :
    P.EligibleDE t := by
  have hPt : P.strictAt t := hs.mpr ht.1
  refine ⟨hPt, ?_, ?_⟩
  · change 2 ≤ P.area.area (D.residue t)
    rw [hat]
    exact ht.2.1
  · have hg := ht.2.2
    unfold eastGap boundary at hg ⊢
    rw [ite_eq_left ht.1] at hg
    rw [ite_eq_left hPt]
    change 0 < t + 1 - (P.area.area (D.residue (t + 1)) : ℤ) -
      (t - (P.area.area (D.residue t) : ℤ)) - 1
    have hle' : (P.area.area (D.residue (t + 1)) : ℤ) ≤ D.area.area (D.residue (t + 1)) := by
      exact_mod_cast hle
    rw [hat]
    lia

end VerticalStripLLT.Circular.Diagram

