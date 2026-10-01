import VerticalStripLLT.Components.DiagramProof.Foundation.ShortFlip
import VerticalStripLLT.Components.FlipTriangle

/-! Terminating elimination of outgoing cover forks by actual directed flips. -/

namespace VerticalStripLLT.Circular.DiagramProof

open scoped BigOperators
open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- Sum of the tails of selected normal edges; strict edges contribute a fixed constant. -/
def selectedTailSum (θ : Orientation D) : ℕ := ∑ e ∈ θ.val, e.tail.val

/-- A fixed bound independent of the selected state. -/
def allTailSum (D : Diagram n) : ℕ := ∑ e : Edge D.area, e.tail.val

theorem selectedTailSum_le_allTailSum (θ : Orientation D) : selectedTailSum θ ≤ allTailSum D := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro _ _ _
  exact Nat.zero_le _

/-- Every forward directed flip increases the potential strictly. -/
theorem selectedTailSum_lt_of_directedFlip (hforward : Forward D)
    {θ η : Orientation D} (w : DirectedFlipWitness D θ η) :
    selectedTailSum θ < selectedTailSum η := by
  have hnot : w.ebc ∉ θ.val.erase w.eab :=
    fun h => w.source_bc_not_mem (Finset.mem_of_mem_erase h)
  have heq := Finset.sum_erase_add (s := θ.val) (fun e : Edge D.area => e.tail.val)
    w.source_ab_mem
  have hlt : w.eab.tail.val < w.ebc.tail.val := by
    rw [← w.short_head_tail]
    exact hforward w.eab
  unfold selectedTailSum
  rw [w.target_eq_source_swap, Finset.sum_insert hnot]
  lia

private theorem exists_directedFlip_of_not_rightUnique_covers (hforward : Forward D)
    (θ : Orientation D) (h : ¬ Relator.RightUnique (Cover θ)) : ∃ η, DirectedFlip D θ η := by
  change ¬ ∀ ⦃a b c : Fin n⦄, Cover θ a b → Cover θ a c → b = c at h
  push Not at h
  obtain ⟨a, b, c, hab, hac, hne⟩ := h
  rcases lt_or_gt_of_ne hne with hbc | hcb
  · obtain ⟨η, w, _⟩ := exists_directedFlip_of_sourceCovers hforward θ a b c hab hac hbc
    exact ⟨η, ⟨w⟩⟩
  · obtain ⟨η, w, _⟩ := exists_directedFlip_of_sourceCovers hforward θ a c b hac hab hcb
    exact ⟨η, ⟨w⟩⟩

/-- Repeated outgoing cover forks terminate; no search through a whole component is used. -/
theorem exists_rightUnique_covers_directed (hforward : Forward D) (θ : Orientation D) :
    ∃ η : Orientation D, Relation.ReflTransGen (DirectedFlip D) θ η ∧
      Relator.RightUnique (Cover η) := by
  generalize hN : allTailSum D - selectedTailSum θ = N
  induction N using Nat.strong_induction_on generalizing θ with
  | h N ih =>
    by_cases hf : Relator.RightUnique (Cover θ)
    · exact ⟨θ, Relation.ReflTransGen.refl, hf⟩
    · obtain ⟨η, hθη⟩ := exists_directedFlip_of_not_rightUnique_covers hforward θ hf
      have hlt := selectedTailSum_lt_of_directedFlip hforward hθη.some
      have hbound := selectedTailSum_le_allTailSum η
      have hmeasure : allTailSum D - selectedTailSum η < N := by lia
      obtain ⟨ξ, hηξ, hξ⟩ := ih _ hmeasure η rfl
      exact ⟨ξ, hηξ.head hθη, hξ⟩

/-- The normalized state is reached by actual flips in the original diagram. -/
theorem exists_rightUnique_covers (hforward : Forward D) (θ : Orientation D) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ Relator.RightUnique (Cover η) := by
  obtain ⟨η, hp, hη⟩ := exists_rightUnique_covers_directed hforward θ
  exact ⟨η, Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) _ _ hp, hη⟩

/-- A minimal vertex with at most one outgoing selected edge is untouched by a directed flip. -/
theorem selected_minimal_row_iff_of_directedFlip (hforward : Forward D)
    {θ η : Orientation D} (w : DirectedFlipWitness D θ η) (z : Fin n)
    (hz : ∀ v, z ≤ v)
    (hrow : ∀ u v, D.edgeData.selected θ.val z u → D.edgeData.selected θ.val z v → u = v)
    (v : Fin n) : D.edgeData.selected η.val z v ↔ D.edgeData.selected θ.val z v := by
  have hbc : w.eab.head < w.ebc.head := w.short_head_tail ▸ hforward w.ebc
  have habz : w.eab.tail ≠ z := by
    intro htail
    have hab : D.edgeData.selected θ.val z w.eab.head :=
      ⟨w.eab, Finset.mem_union_right _ w.source_ab_mem, htail, rfl⟩
    have hac : D.edgeData.selected θ.val z w.ebc.head :=
      ⟨w.longEdge, w.longEdge_mem, w.longEdge_tail.symm.trans htail, w.longEdge_head.symm⟩
    exact hbc.ne (hrow _ _ hab hac)
  have hbcz : w.ebc.tail ≠ z := by
    intro htail
    have hlt : w.eab.tail < z := (hforward w.eab).trans_eq
      (w.short_head_tail.trans htail)
    exact not_lt_of_ge (hz _) hlt
  have hmem (e : Edge D.area) (he : e.tail = z) :
      e ∈ D.strict ∪ η.val ↔ e ∈ D.strict ∪ θ.val := by
    have hneab : e ≠ w.eab := fun h => habz (h ▸ he)
    have hnebc : e ≠ w.ebc := fun h => hbcz (h ▸ he)
    rw [w.full_target_eq_source_swap]
    simp [hneab, hnebc]
  constructor
  · rintro ⟨e, he, het, heh⟩
    exact ⟨e, (hmem e het).mp he, het, heh⟩
  · rintro ⟨e, he, het, heh⟩
    exact ⟨e, (hmem e het).mpr he, het, heh⟩

/-- The minimal one-edge row remains fixed throughout outgoing-fork normalization. -/
theorem selected_minimal_row_iff_of_directedReachable (hforward : Forward D)
    {θ η : Orientation D} (hp : Relation.ReflTransGen (DirectedFlip D) θ η) (z : Fin n)
    (hz : ∀ v, z ≤ v)
    (hrow : ∀ u v, D.edgeData.selected θ.val z u → D.edgeData.selected θ.val z v → u = v) :
    ∀ v, D.edgeData.selected η.val z v ↔ D.edgeData.selected θ.val z v := by
  induction hp with
  | refl => intro _; exact Iff.rfl
  | @tail ξ η _ hstep ih =>
    have hrowξ : ∀ u v, D.edgeData.selected ξ.val z u →
        D.edgeData.selected ξ.val z v → u = v := by
      intro u v hu hv
      exact hrow u v ((ih u).mp hu) ((ih v).mp hv)
    intro v
    exact (selected_minimal_row_iff_of_directedFlip hforward hstep.some z hz hrowξ v).trans
      (ih v)

/-- The normalized state retains the prescribed minimal row as well as its actual component. -/
theorem exists_rightUnique_covers_preserving_minimal_row (hforward : Forward D)
    (θ : Orientation D) (z : Fin n) (hz : ∀ v, z ≤ v)
    (hrow : ∀ u v, D.edgeData.selected θ.val z u → D.edgeData.selected θ.val z v → u = v) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ Relator.RightUnique (Cover η) ∧
      ∀ v, D.edgeData.selected η.val z v ↔ D.edgeData.selected θ.val z v := by
  obtain ⟨η, hp, hη⟩ := exists_rightUnique_covers_directed hforward θ
  exact ⟨η, Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) _ _ hp, hη,
    selected_minimal_row_iff_of_directedReachable hforward hp z hz hrow⟩

end

end VerticalStripLLT.Circular.DiagramProof
