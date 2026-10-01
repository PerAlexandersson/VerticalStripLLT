import VerticalStripLLT.Components.DiagramProof.Complete.Interval
import VerticalStripLLT.Components.DiagramProof.Complete.ChainOpening

/-! Opening a complete chain to an interval, with exact selected edges. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- Open all adjacent chain edges from `b` upwards toward the least vertex. -/
def openCompleteChain {n : ℕ} (θ : Orientation (completeDiagram n))
    (b : Fin (n + 1)) (hb : 0 < b) : Orientation (completeDiagram n) :=
  ofSelectedRelation (complete_forward n)
    (fun u v => (u = 0 ∧ b ≤ v) ∨
      ((completeDiagram n).edgeData.selected θ.val u v ∧
        ¬ (b ≤ u ∧ u.val + 1 = v.val)))
    (by
      intro u v h
      apply (complete_naturalEdge_iff n u v).mpr
      rcases h with ⟨rfl, hv⟩ | ⟨h, _⟩
      · exact hb.trans_le hv
      · exact θ.selected_lt_of_forward (complete_forward n) h)
    (by simp)

@[simp]
theorem openCompleteChain_selected {n : ℕ} (θ : Orientation (completeDiagram n))
    (b : Fin (n + 1)) (hb : 0 < b) (u v : Fin (n + 1)) :
    (completeDiagram n).edgeData.selected (openCompleteChain θ b hb).val u v ↔
      (u = 0 ∧ b ≤ v) ∨ ((completeDiagram n).edgeData.selected θ.val u v ∧
        ¬ (b ≤ u ∧ u.val + 1 = v.val)) :=
  selected_ofSelectedRelation ..

/-- The opened root row consists exactly of the vertices at or above the opening. -/
theorem openCompleteChain_row {n : ℕ} (θ : Orientation (completeDiagram n))
    (b : Fin (n + 1)) (hb : 0 < b)
    (hrow : ∀ v, (completeDiagram n).edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (v : Fin (n + 1)) :
    (completeDiagram n).edgeData.selected (openCompleteChain θ b hb).val 0 v ↔ b ≤ v := by
  rw [openCompleteChain_selected, hrow]
  have hb0 : ¬ b ≤ 0 := not_le_of_gt hb
  simp only [true_and, hb0, false_and, not_false_eq_true, and_true]
  constructor
  · rintro (h | rfl)
    · exact h
    · exact Fin.le_last b
  · exact Or.inl

/-- Opening does not change a positive edge whose tail is below the threshold. -/
theorem openCompleteChain_below {n : ℕ} (θ : Orientation (completeDiagram n))
    (b : Fin (n + 1)) (hb : 0 < b) (u v : Fin (n + 1)) (hu : 0 < u) (hub : u < b) :
    (completeDiagram n).edgeData.selected (openCompleteChain θ b hb).val u v ↔
      (completeDiagram n).edgeData.selected θ.val u v := by
  rw [openCompleteChain_selected]
  simp [hu.ne.symm, not_le_of_gt hub]

/-- Opening two states with the same exterior preserves that agreement. -/
theorem openCompleteChain_outside {k n : ℕ} (ι : Fin (k + 1) ↪o Fin (n + 1))
    (θ η : Orientation (completeDiagram n)) (b : Fin (n + 1)) (hb : 0 < b)
    (hout : ∀ u v, (¬ ∃ a c, ι a = u ∧ ι c = v) →
      ((completeDiagram n).edgeData.selected θ.val u v ↔
        (completeDiagram n).edgeData.selected η.val u v))
    (u v : Fin (n + 1)) (huv : ¬ ∃ a c, ι a = u ∧ ι c = v) :
    (completeDiagram n).edgeData.selected (openCompleteChain θ b hb).val u v ↔
      (completeDiagram n).edgeData.selected (openCompleteChain η b hb).val u v := by
  rw [openCompleteChain_selected, openCompleteChain_selected, hout u v huv]

/-- The explicit opened state is reached by the descending actual flips of CC3. -/
theorem reachable_openCompleteChain_of_chain_above {n : ℕ} (θ : Orientation (completeDiagram n))
    (b : Fin (n + 1)) (hb : 0 < b)
    (hrow : ∀ v, (completeDiagram n).edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hchain : ∀ u v : Fin (n + 1), b ≤ u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected θ.val u v) :
    Relation.ReflTransGen (Flip (completeDiagram n)) θ (openCompleteChain θ b hb) := by
  obtain ⟨η, hp, hη⟩ := exists_chain_opening_of_chain_above (complete_forward n) θ b
    (Fin.last n) hb (Fin.le_last b) hrow (fun u v hbu huv _ => hchain u v hbu huv)
  have heq : η = openCompleteChain θ b hb := by
    apply fullSelection_injective
    ext e
    rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected,
      hη, openCompleteChain_selected]
    simp only [Fin.le_last, and_true]
  exact heq ▸ hp

theorem reachable_openCompleteChain {n : ℕ} (θ : Orientation (completeDiagram n))
    (b : Fin (n + 1)) (hb : 0 < b)
    (hrow : ∀ v, (completeDiagram n).edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hchain : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected θ.val u v) :
    Relation.ReflTransGen (Flip (completeDiagram n)) θ (openCompleteChain θ b hb) := by
  exact reachable_openCompleteChain_of_chain_above θ b hb hrow
    (fun u v hbu huv => hchain u v (hb.trans_le hbu) huv)

/-- The positive interval endpoint is a valid opening threshold. -/
theorem intervalEmbed_last_pos {n a m : ℕ} (ha : 0 < a) (hb : a + m ≤ n) :
    0 < intervalEmbed a m ha hb (Fin.last (m + 1)) := by
  change 0 < a + m
  lia

/-- Restricting the opened state gives exactly the smaller chain's extreme root edge. -/
theorem openCompleteChain_interval_row {n a m : ℕ} (ha : 0 < a) (hb : a + m ≤ n)
    (θ : Orientation (completeDiagram n))
    (hrow : ∀ v, (completeDiagram n).edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (v : Fin (m + 2)) :
    (completeDiagram (m + 1)).edgeData.selected
      (completeRestrictAlong (intervalEmbed a m ha hb)
        (openCompleteChain θ (intervalEmbed a m ha hb (Fin.last (m + 1)))
          (intervalEmbed_last_pos ha hb))).val 0 v ↔ v = Fin.last (m + 1) := by
  rw [completeRestrictAlong_selected, intervalEmbed_zero, openCompleteChain_row _ _ _ hrow]
  rw [(intervalEmbed a m ha hb).le_iff_le]
  exact ⟨fun h => le_antisymm (Fin.le_last v) h, fun h => h ▸ le_rfl⟩

/-- All consecutive positive edges of the smaller chain survive opening and restriction. -/
theorem openCompleteChain_interval_chain {n a m : ℕ} (ha : 0 < a) (hb : a + m ≤ n)
    (θ : Orientation (completeDiagram n))
    (hchain : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected θ.val u v)
    (u v : Fin (m + 2)) (hu : 0 < u) (huv : u.val + 1 = v.val) :
    (completeDiagram (m + 1)).edgeData.selected
      (completeRestrictAlong (intervalEmbed a m ha hb)
        (openCompleteChain θ (intervalEmbed a m ha hb (Fin.last (m + 1)))
          (intervalEmbed_last_pos ha hb))).val u v := by
  let ι := intervalEmbed a m ha hb
  have huvlt : u < v := by change u.val < v.val; lia
  have hu0 : 0 < ι u := by simpa [ι] using ι.strictMono hu
  have hulast : ι u < ι (Fin.last (m + 1)) :=
    ι.strictMono (huvlt.trans_le (Fin.le_last v))
  have hstep : (ι u).val + 1 = (ι v).val := by
    cases u using Fin.cases with
    | zero => exact (lt_irrefl _ hu).elim
    | succ u =>
      cases v using Fin.cases with
      | zero => exact (not_lt_of_ge (Fin.zero_le _) huvlt).elim
      | succ v =>
        change a + u.val + 1 = a + v.val
        change u.val + 1 + 1 = v.val + 1 at huv
        lia
  rw [completeRestrictAlong_selected]
  exact (openCompleteChain_below θ _ (intervalEmbed_last_pos ha hb) _ _ hu0 hulast).mpr
    (hchain _ _ hu0 hstep)

end

end VerticalStripLLT.Circular.DiagramProof
