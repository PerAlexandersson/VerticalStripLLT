import VerticalStripLLT.Circular.NDSeparatedDiagrams
set_option backward.isDefEq.respectTransparency false


/-! The shortened diagrams `N′`, `J′`, `R`, the corner deletion `E′` of `Q`, and the exact
identifications: `N′ = unstrict g in Q`, strictify/delete the row-`x` corner of `E′` give `R`
and `J′`, and `Q` has the rows of the DN target of `S`. Doubled-area drops. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ}

namespace NDSeparatedHyp

variable {D : Diagram n} {t x : ℤ} {k : ℕ} (H : NDSeparatedHyp D t x k)

theorem dQ_hx1 : H.dQ.strictAt (x + 1) := (H.dQ_strictAt _).mpr H.hx1

/-- The terminal strict edge viewed in `Q`. -/
noncomputable def gQ : Edge H.dQ.area := Classical.choose H.dQ_hx1

theorem gQ_mem : H.gQ ∈ H.dQ.strict := (Classical.choose_spec H.dQ_hx1).1

theorem gQ_head : H.gQ.head = D.residue (x + 1) := (Classical.choose_spec H.dQ_hx1).2

/-- `E′`: the terminal strict corner deleted from `Q`. -/
noncomputable def dEs : Diagram n :=
  H.dQ.deleteCorner H.gQ (H.dQ.strict_corner H.gQ H.gQ_mem)

theorem dEs_area : H.dEs.area.area = Function.update (Function.update D.area.area
    (D.residue t) (D.area.area (D.residue t) - 1)) (D.residue (x + 1))
    (D.area.area (D.residue (x + 1)) - 1) := by
  rw [dEs, ndSep_deleteCorner_area, H.gQ_head, H.dQ_area,
    Function.update_of_ne H.res_t_ne_x1.symm]

theorem dEs_strictAt (z : ℤ) :
    H.dEs.strictAt z ↔ D.strictAt z ∧ D.residue z ≠ D.residue (x + 1) := by
  rw [dEs, deleteStrictCorner_strictAt_iff _ _ H.gQ_mem, H.dQ_strictAt, H.gQ_head]
  exact Iff.rfl

theorem dEs_area_x : H.dEs.area.area (D.residue x) = D.area.area (D.residue x) := by
  rw [H.dEs_area, Function.update_of_ne H.res_x1_ne_x.symm,
    Function.update_of_ne H.res_t_ne_x.symm]

theorem dEs_area_x1 : H.dEs.area.area (D.residue (x + 1)) = D.area.area (D.residue x) := by
  rw [H.dEs_area, Function.update_self, H.area_x1]
  simp

theorem dEs_pos : 0 < H.dEs.area.area (D.residue x) := by
  rw [H.dEs_area_x]
  exact H.area_x_pos

/-- The row-`x` corner of `E′`. -/
noncomputable def ellEs : Edge H.dEs.area := H.dEs.ndSepCornerAt (D.residue x) H.dEs_pos

theorem ellEs_corner : IsCorner H.ellEs := by
  apply H.dEs.ndSepCornerAt_isCorner
  rw [next_congr H.dEs.area D.area, ← D.residue_succ, H.dEs_area_x1, H.dEs_area_x]

theorem ellEs_not_mem : H.ellEs ∉ H.dEs.strict :=
  H.dEs.ndSepCornerAt_not_mem (z := x) H.dEs_pos (fun h => H.hx ((H.dEs_strictAt x).mp h).1)

/-- `N′`: the root shortened in `N`. -/
noncomputable def dNs : Diagram n := H.dN.shortenEligible t H.dN_eligible

/-- `J′`: the root shortened in `J`. -/
noncomputable def dJs : Diagram n := H.dJ.shortenEligible t H.dJ_eligible

/-- `R`: the root shortened in `S`. -/
noncomputable def dR : Diagram n := H.dS.shortenEligible t H.dS_eligible

/-- `N′` is `Q` with `g` made normal. -/
theorem dNs_eq : H.dNs = H.dQ.unstrict H.gQ H.gQ_mem := by
  apply ext_of_area_eq_of_strictAt
  · rw [dNs, shortenEligible_area, unstrict_area, H.dQ_area]
    rfl
  · intro z
    rw [dNs, shortenEligible_strictAt_iff, H.dN_strictAt, unstrict_strictAt_iff, H.dQ_strictAt,
      H.gQ_head]
    exact Iff.rfl

/-- Strictifying the row-`x` corner of `E′` gives `R`. -/
theorem dEs_strictify_eq : H.dEs.strictify H.ellEs H.ellEs_corner = H.dR := by
  apply ext_of_area_eq_of_strictAt
  · change H.dEs.area.area = _
    rw [dR, shortenEligible_area, H.dEs_area]
    change _ = Function.update H.dS.area.area (D.residue t) (H.dS.area.area (D.residue t) - 1)
    rw [H.dS_area_eq H.res_t_ne_x1, H.dS_area, Function.update_comm H.res_t_ne_x1]
  · intro z
    rw [ndSep_strictify_strictAt_iff, H.dEs_strictAt, dR, shortenEligible_strictAt_iff,
      H.dS_strictAt]
    exact Iff.rfl

/-- Deleting the row-`x` corner of `E′` gives `J′`. -/
theorem dEs_deleteCorner_eq : H.dEs.deleteCorner H.ellEs H.ellEs_corner = H.dJs := by
  apply ext_of_area_eq_of_strictAt
  · rw [ndSep_deleteCorner_area, dJs, shortenEligible_area]
    change Function.update H.dEs.area.area (D.residue x) (H.dEs.area.area (D.residue x) - 1) =
      Function.update H.dJ.area.area (D.residue t) (H.dJ.area.area (D.residue t) - 1)
    rw [H.dEs_area_x, H.dJ_area_eq H.res_t_ne_x H.res_t_ne_x1, H.dEs_area, H.dJ_area,
      Function.update_comm H.res_t_ne_x1, Function.update_comm H.res_t_ne_x]
  · intro z
    rw [ndSep_deleteCorner_strictAt_iff_of_not_mem _ _ _ H.ellEs_not_mem, H.dEs_strictAt, dJs,
      shortenEligible_strictAt_iff, H.dJ_strictAt]

/-- `Q` has exactly the rows of the DN target of `S` for the root `t` and terminal `x`. -/
theorem dQ_isDNTarget : IsDNTarget H.dS t x H.dQ := by
  constructor
  · rw [H.dQ_area]
    change _ = Function.update (Function.update H.dS.area.area (D.residue (x + 1))
      (H.dS.area.area (D.residue x) + 1)) (D.residue t) (H.dS.area.area (D.residue t) - 1)
    rw [H.dS_area_eq H.res_x1_ne_x.symm, H.dS_area_eq H.res_t_ne_x1, H.dS_area,
      Function.update_idem, ← H.area_x1, Function.update_eq_self]
  · intro z
    rw [H.dQ_strictAt, H.dS_strictAt]
    change D.strictAt z ↔ (((D.strictAt z ∧ D.residue z ≠ D.residue (x + 1)) ∨
      D.residue z = D.residue x) ∧ D.residue z ≠ D.residue x) ∨
        D.residue z = D.residue (x + 1)
    constructor
    · intro hz
      by_cases h1 : D.residue z = D.residue (x + 1)
      · exact Or.inr h1
      · exact Or.inl ⟨Or.inl ⟨hz, h1⟩, D.residue_ne_of_strictAt hz H.hx⟩
    · rintro (⟨(⟨hz, -⟩ | hz), hne⟩ | hz)
      · exact hz
      · exact absurd hz hne
      · exact (D.strictAt_congr_residue hz).mpr H.hx1

/-! ### Doubled areas -/

theorem ell_val_not_mem : H.ell.1 ∉ D.strictVals.erase H.g.1 := by
  intro hm
  obtain ⟨e, he, hee⟩ := (D.mem_strictVals _).mp (Finset.mem_of_mem_erase hm)
  exact H.hx ⟨e, he, congrArg Prod.fst hee⟩

theorem dS_doubledArea : H.dS.doubledArea + 2 = D.doubledArea := by
  apply doubledArea_of_lower_one (D.residue (x + 1)) (by rw [H.area_x1]; lia) H.dS_area
  have hE : H.dE.strictVals = D.strictVals.erase H.g.1 := D.strictVals_deleteCorner _ _
  have hg : H.g.1 ∈ D.strictVals := (D.val_mem_strictVals _).mpr H.g_mem
  rw [← card_strictVals, ← card_strictVals, dS, strictVals_strictify, hE,
    Finset.card_insert_of_notMem H.ell_val_not_mem, Finset.card_erase_of_mem hg]
  have := Finset.card_pos.mpr ⟨_, hg⟩
  lia

theorem dR_doubledArea : H.dR.doubledArea + 4 = D.doubledArea := by
  have h1 := H.dS.shortenEligible_doubledArea t H.dS_eligible
  have h2 := H.dS_doubledArea
  change H.dR.doubledArea + 2 = H.dS.doubledArea at h1
  lia

theorem dQ_doubledArea : H.dQ.doubledArea + 2 = D.doubledArea :=
  D.shortenEligible_doubledArea t H.ht

end NDSeparatedHyp

end VerticalStripLLT.Circular.Diagram


