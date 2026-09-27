import VerticalStripLLT.Circular.LiftCover

/-! Rank certificates for covers in the full circular integer lift. -/

namespace VerticalStripLLT.Circular

namespace Diagram

variable {n : ℕ} {D : Diagram n} {A : Finset (Edge D.area)}

private theorem rank_le_of_liftReach (rank : Fin n → ℕ)
    (hrank : ∀ ⦃u v⦄, D.edgeData.selected A u v → rank u < rank v)
    {x y : ℤ} (h : Relation.ReflTransGen (D.liftStep A) x y) :
    rank (D.residue x) ≤ rank (D.residue y) := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    exact ih.trans (Nat.le_of_lt (hrank (D.liftStep_selected hstep)))

/-- A nontrivial lifted path strictly increases every rank that increases on
selected projected edges. -/
theorem rank_lt_of_liftReach (rank : Fin n → ℕ)
    (hrank : ∀ ⦃u v⦄, D.edgeData.selected A u v → rank u < rank v)
    {x y : ℤ} (hxy : x < y) (h : Relation.ReflTransGen (D.liftStep A) x y) :
    rank (D.residue x) < rank (D.residue y) := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨z, hxz, hzy⟩
  · exact False.elim (lt_irrefl x hxy)
  · exact (hrank (D.liftStep_selected hxz)).trans_le
      (rank_le_of_liftReach rank hrank hzy)

/-- A rank gap excludes every factorization of a lifted selected step, so the
step is a cover in the full integer lift relation. -/
theorem liftCover_of_liftStep_rank_gap (rank : Fin n → ℕ)
    (hrank : ∀ ⦃u v⦄, D.edgeData.selected A u v → rank u < rank v)
    {x y : ℤ} (hstep : D.liftStep A x y)
    (hgap : ∀ z, x < z → z < y →
      ¬ (rank (D.residue x) < rank (D.residue z) ∧
        rank (D.residue z) < rank (D.residue y))) :
    D.liftCover A x y := by
  have hxy : x < y := by
    have hpos := (D.liftStep_bounds hstep).1
    lia
  refine ⟨hxy, Relation.ReflTransGen.single hstep, ?_⟩
  intro z hxz hzy hfactor
  exact hgap z hxz hzy ⟨rank_lt_of_liftReach rank hrank hxz hfactor.1,
    rank_lt_of_liftReach rank hrank hzy hfactor.2⟩

/-- Consecutive rank values give the rank gap required for a lifted cover. -/
theorem liftCover_of_liftStep_rank_succ (rank : Fin n → ℕ)
    (hrank : ∀ ⦃u v⦄, D.edgeData.selected A u v → rank u < rank v)
    {x y : ℤ} (hstep : D.liftStep A x y)
    (hsucc : rank (D.residue y) = rank (D.residue x) + 1) :
    D.liftCover A x y := by
  apply liftCover_of_liftStep_rank_gap rank hrank hstep
  intro z _ _ hbetween
  rw [hsucc] at hbetween
  lia

end Diagram

end VerticalStripLLT.Circular
