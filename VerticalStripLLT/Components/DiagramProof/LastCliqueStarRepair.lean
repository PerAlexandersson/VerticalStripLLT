import VerticalStripLLT.Components.DiagramProof.CliqueBlockBounds

/-! Connectivity in the displayed star and after replacing one of its edges. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

/-- A selected edge other than the removed one survives an exact exchange. -/
theorem selected_of_exchange_of_ne (θ η : Orientation D) (e f : Edge D.area)
    (hfull : fullSelection η = insert f ((fullSelection θ).erase e))
    {u v : Fin n} (hne : u ≠ e.tail ∨ v ≠ e.head)
    (hsel : D.edgeData.selected θ.val u v) : D.edgeData.selected η.val u v := by
  classical
  obtain ⟨r, hr, hrt, hrh⟩ := hsel
  have hre : r ≠ e := by
    rintro rfl
    exact hne.elim (fun h => h hrt.symm) (fun h => h hrh.symm)
  refine ⟨r, ?_, hrt, hrh⟩
  change r ∈ fullSelection η
  rw [hfull]
  exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hre, hr⟩)

/-- Every vertex of the displayed terminal star is in the last-corner block. -/
theorem cliqueBlock_connected_of_terminal_star (hD : Forward D)
    (g : Edge D.area) (θ : Orientation D)
    (hstar : ∀ v, g.tail ≤ v → v < g.head → D.edgeData.selected θ.val v g.head) :
    ∀ v, g.tail ≤ v → v ≤ g.head →
      Relation.EqvGen (cliqueBlockRelation g θ) g.tail v := by
  have hto (v : Fin n) (hav : g.tail ≤ v) (hve : v ≤ g.head) :
      Relation.EqvGen (cliqueBlockRelation g θ) v g.head := by
    rcases hve.eq_or_lt with rfl | hve
    · exact .refl _
    · exact .rel _ _ ((cliqueBlockRelation_iff_of_forward hD g θ v g.head).mpr
        ⟨hav, le_rfl, hstar v hav hve⟩)
  intro v hav hve
  exact .trans _ _ _ (hto g.tail le_rfl (hD g).le) (.symm _ _ (hto v hav hve))

/-- If one star edge is missing, a connection to another internal vertex repairs it. -/
theorem cliqueBlock_connected_of_repaired_star (hD : Forward D)
    (g : Edge D.area) (θ : Orientation D) (c d : Fin n)
    (had : g.tail < d) (hde : d < g.head) (hdc : d ≠ c)
    (hcorner : D.edgeData.selected θ.val g.tail g.head)
    (hstar : ∀ v, g.tail < v → v < g.head → v ≠ c →
      D.edgeData.selected θ.val v g.head)
    (hjoin : Relation.EqvGen (cliqueBlockRelation g θ) c d) :
    ∀ v, g.tail ≤ v → v ≤ g.head →
      Relation.EqvGen (cliqueBlockRelation g θ) g.tail v := by
  have htail : Relation.EqvGen (cliqueBlockRelation g θ) g.tail g.head :=
    .rel _ _ ((cliqueBlockRelation_iff_of_forward hD g θ g.tail g.head).mpr
      ⟨le_rfl, le_rfl, hcorner⟩)
  have hcto : Relation.EqvGen (cliqueBlockRelation g θ) c g.head :=
    .trans _ _ _ hjoin (.rel _ _
      ((cliqueBlockRelation_iff_of_forward hD g θ d g.head).mpr
        ⟨had.le, le_rfl, hstar d had hde hdc⟩))
  intro v hav hve
  have hto : Relation.EqvGen (cliqueBlockRelation g θ) v g.head := by
    rcases hav.eq_or_lt with rfl | hav
    · exact htail
    rcases hve.eq_or_lt with rfl | hve
    · exact .refl _
    by_cases hvc : v = c
    · simpa only [hvc] using hcto
    · exact .rel _ _ ((cliqueBlockRelation_iff_of_forward hD g θ v g.head).mpr
        ⟨hav.le, le_rfl, hstar v hav hve hvc⟩)
  exact .trans _ _ _ htail (.symm _ _ hto)

end VerticalStripLLT.Circular.DiagramProof
