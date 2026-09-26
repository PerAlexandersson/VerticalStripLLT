import VerticalStripLLT.Circular.LiftCover
import VerticalStripLLT.Circular.HRV

/-! Global circular LLT flips and their complete lifted-reachability components. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators

variable {n : ℕ}

/-- Data witnessing one directed circular LLT flip in the full integer cover. -/
structure DirectedFlipWitness (D : Diagram n) (θ η : Orientation D) where
  a : ℤ
  b : ℤ
  c : ℤ
  cyclicWindow : a < b ∧ b < c ∧ c < a + (n : ℤ)
  eab : Edge D.area
  ebc : Edge D.area
  eab_normal : eab ∈ D.edgeData.normalEdges
  ebc_normal : ebc ∈ D.edgeData.normalEdges
  ab_lift : D.naturalLift eab a b
  bc_lift : D.naturalLift ebc b c
  source_ab : D.liftCover θ.val a b
  source_ac : D.liftCover θ.val a c
  source_not_bc : ¬ D.liftCover θ.val b c
  target_ac : D.liftCover η.val a c
  target_bc : D.liftCover η.val b c
  target_not_ab : ¬ D.liftCover η.val a b
  agree_elsewhere : ∀ e, e ≠ eab → e ≠ ebc → (e ∈ θ.val ↔ e ∈ η.val)

/-- A directed flip exists when its lifted cover witness exists. -/
def DirectedFlip (D : Diagram n) (θ η : Orientation D) : Prop :=
  Nonempty (DirectedFlipWitness D θ η)

/-- The undirected circular flip relation. -/
def Flip (D : Diagram n) (θ η : Orientation D) : Prop :=
  DirectedFlip D θ η ∨ DirectedFlip D η θ

theorem flip_symm (D : Diagram n) {θ η : Orientation D} (h : Flip D θ η) : Flip D η θ := by
  exact h.elim Or.inr Or.inl

namespace DirectedFlipWitness

variable {D : Diagram n} {θ η : Orientation D}

private theorem mem_orientation_of_normal {A : Finset (Edge D.area)}
    {e : Edge D.area}
    (he : e ∈ D.edgeData.normalEdges) (h : e ∈ D.strict ∪ A) : e ∈ A := by
  rcases Finset.mem_union.mp h with hs | ha
  · have hns : e ∉ D.strict := (Finset.mem_sdiff.mp he).2
    exact (hns hs).elim
  · exact ha

theorem source_ab_mem (w : DirectedFlipWitness D θ η) : w.eab ∈ θ.val := by
  apply mem_orientation_of_normal w.eab_normal
  exact D.mem_selected_of_naturalLift_of_liftCover w.ab_lift w.source_ab

theorem target_bc_mem (w : DirectedFlipWitness D θ η) : w.ebc ∈ η.val := by
  apply mem_orientation_of_normal w.ebc_normal
  exact D.mem_selected_of_naturalLift_of_liftCover w.bc_lift w.target_bc

theorem source_bc_not_mem (w : DirectedFlipWitness D θ η) : w.ebc ∉ θ.val := by
  intro hbc
  have hstep_ab : D.liftStep θ.val w.a w.b :=
    D.liftCover_liftStep w.source_ab
  have hstep_bc : D.liftStep θ.val w.b w.c := by
    apply D.liftStep_of_naturalLift_of_mem (Finset.mem_union.mpr (Or.inr hbc))
    exact w.bc_lift
  rcases w.source_ac with ⟨_, _, hno⟩
  apply hno w.b w.cyclicWindow.1 w.cyclicWindow.2.1
  exact ⟨Relation.ReflTransGen.single hstep_ab,
    Relation.ReflTransGen.single hstep_bc⟩

theorem target_ab_not_mem (w : DirectedFlipWitness D θ η) : w.eab ∉ η.val := by
  intro hab
  have hstep_ab : D.liftStep η.val w.a w.b := by
    apply D.liftStep_of_naturalLift_of_mem (Finset.mem_union.mpr (Or.inr hab))
    exact w.ab_lift
  have hstep_bc : D.liftStep η.val w.b w.c :=
    D.liftCover_liftStep w.target_bc
  rcases w.target_ac with ⟨_, _, hno⟩
  apply hno w.b w.cyclicWindow.1 w.cyclicWindow.2.1
  exact ⟨Relation.ReflTransGen.single hstep_ab,
    Relation.ReflTransGen.single hstep_bc⟩

theorem distinct_orbits (w : DirectedFlipWitness D θ η) : w.eab ≠ w.ebc := by
  intro h
  exact w.source_bc_not_mem (h ▸ w.source_ab_mem)

theorem target_eq_source_swap (w : DirectedFlipWitness D θ η) :
    η.val = insert w.ebc (θ.val.erase w.eab) := by
  classical
  ext e
  by_cases hab : e = w.eab
  · subst e
    simp [w.target_ab_not_mem, w.distinct_orbits]
  by_cases hbc : e = w.ebc
  · subst e
    simp [w.target_bc_mem]
  · simp [hab, hbc, w.agree_elsewhere e hab hbc]

theorem card_eq (w : DirectedFlipWitness D θ η) : θ.val.card = η.val.card := by
  classical
  rw [w.target_eq_source_swap]
  have hnot : w.ebc ∉ θ.val.erase w.eab := by
    simp [w.source_bc_not_mem]
  rw [Finset.card_insert_of_notMem hnot, Finset.card_erase_add_one w.source_ab_mem]

end DirectedFlipWitness

theorem directedFlip_card_eq {D : Diagram n} {θ η : Orientation D}
    (h : DirectedFlip D θ η) : θ.val.card = η.val.card := by
  exact h.some.card_eq

theorem flip_card_eq {D : Diagram n} {θ η : Orientation D}
    (h : Flip D θ η) : θ.val.card = η.val.card := by
  rcases h with h | h
  · exact directedFlip_card_eq h
  · exact (directedFlip_card_eq h).symm

theorem flip_reachable_card_eq {D : Diagram n} {θ η : Orientation D}
    (h : Relation.ReflTransGen (Flip D) θ η) : θ.val.card = η.val.card := by
  induction h with
  | refl => rfl
  | tail hξη hζη ih => exact ih.trans (flip_card_eq hζη)

/-- The complete component of an orientation under all global circular flips. -/
noncomputable def flipComponent (D : Diagram n) (θ : Orientation D) : Finset (Orientation D) := by
  classical
  exact Finset.univ.filter (Relation.ReflTransGen (Flip D) θ)

theorem mem_flipComponent_iff {D : Diagram n} {θ η : Orientation D} :
    η ∈ flipComponent D θ ↔ Relation.ReflTransGen (Flip D) θ η := by
  classical
  simp [flipComponent]

theorem card_eq_of_mem_flipComponent {D : Diagram n} {θ η : Orientation D}
    (h : η ∈ flipComponent D θ) : θ.val.card = η.val.card :=
  flip_reachable_card_eq (mem_flipComponent_iff.mp h)

/-- The independent elementary expression summed over one complete flip component. -/
noncomputable def componentHRV (D : Diagram n) (θ : Orientation D) : EExpansion :=
  ∑ η ∈ flipComponent D θ, η.hrvMonomial

end VerticalStripLLT.Circular
