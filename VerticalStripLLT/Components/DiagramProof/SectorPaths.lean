import VerticalStripLLT.Components.DiagramProof.SubsetBands

/-! Sector paths with additive feasibility bounds for the core edge count. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V : Type*} [DecidableEq V]

/-- A selected sector and a feasible core size, with one fixed attachment edge. -/
def FeasibleSector (J : Finset V) (r m s : ℕ) :=
  {S : Finset V // S ⊆ J ∧ ∃ t, r ≤ t ∧ t ≤ m ∧ t + 1 + S.card = s}

/-- Insert or delete one sector element, keeping both endpoints feasible. -/
def feasibleSectorStep {J : Finset V} {r m s : ℕ}
    (S T : FeasibleSector J r m s) : Prop :=
  (∃ x, x ∉ S.val ∧ T.val = insert x S.val) ∨
    ∃ x, x ∈ S.val ∧ T.val = S.val.erase x

private theorem feasible_card_iff_band (r m s p k : ℕ)
    (hs : r + 1 ≤ s) (hk : k ≤ p) :
    (∃ t, r ≤ t ∧ t ≤ m ∧ t + 1 + k = s) ↔
      s - (m + 1) ≤ k ∧ k ≤ min p (s - (r + 1)) := by
  constructor
  · rintro ⟨t, hrt, htm, heq⟩
    refine ⟨?_, le_min hk ?_⟩ <;> lia
  · rintro ⟨hlower, hupper⟩
    have hkupper := hupper.trans (min_le_right _ _)
    refine ⟨s - (k + 1), ?_, ?_, ?_⟩ <;> lia

private theorem feasible_band_connected (J : Finset V) (r m s : ℕ)
    (hroom : r < m)
    (S T : SubsetBand J (s - (m + 1)) (min J.card (s - (r + 1)))) :
    Relation.ReflTransGen subsetBandStep S T := by
  apply subsetBand_connected
  have hLU := S.property.2.1.trans S.property.2.2
  rcases lt_or_eq_of_le hLU with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    by_cases hzero : s - (m + 1) = 0
    · exact Or.inl hzero
    · right
      by_cases hp : J.card ≤ s - (r + 1)
      · simpa only [min_eq_left hp] using heq
      · rw [min_eq_right (le_of_not_ge hp)] at heq
        lia

/-- A core with at least two feasible sizes connects all feasible sectors.
The empty ambient sector is also allowed when the core has just one size. -/
theorem feasibleSector_connected {J : Finset V} {r m s : ℕ}
    (hroom : r < m ∨ J = ∅) (S T : FeasibleSector J r m s) :
    Relation.ReflTransGen feasibleSectorStep S T := by
  rcases hroom with hroom | hJ
  · obtain ⟨t, hrt, _, heq⟩ := S.property.2
    have hs : r + 1 ≤ s := by lia
    let B := SubsetBand J (s - (m + 1)) (min J.card (s - (r + 1)))
    let toBand : FeasibleSector J r m s → B := fun A =>
      ⟨A.val, A.property.1, (feasible_card_iff_band r m s J.card A.val.card hs
        (Finset.card_le_card A.property.1)).mp A.property.2⟩
    let fromBand : B → FeasibleSector J r m s := fun A =>
      ⟨A.val, A.property.1, (feasible_card_iff_band r m s J.card A.val.card hs
        (Finset.card_le_card A.property.1)).mpr A.property.2⟩
    have hp := feasible_band_connected J r m s hroom (toBand S) (toBand T)
    have liftPath {A C : B} (h : Relation.ReflTransGen subsetBandStep A C) :
        Relation.ReflTransGen feasibleSectorStep (fromBand A) (fromBand C) := by
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih => exact ih.tail hstep
    exact liftPath hp
  · have hS : S.val = ∅ := Finset.subset_empty.mp (hJ ▸ S.property.1)
    have hT : T.val = ∅ := Finset.subset_empty.mp (hJ ▸ T.property.1)
    have hST : S = T := Subtype.ext (hS.trans hT.symm)
    exact hST ▸ Relation.ReflTransGen.refl

end VerticalStripLLT.Circular.DiagramProof
