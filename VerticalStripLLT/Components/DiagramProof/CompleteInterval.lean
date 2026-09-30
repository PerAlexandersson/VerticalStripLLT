import VerticalStripLLT.Components.DiagramProof.CompleteSubdiagram
import VerticalStripLLT.Components.DiagramProof.PathRestriction

/-! The ordered vertices `0,a,a+1,...,a+m` of a complete subdiagram. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- Embed the least vertex followed by a consecutive interval of positive vertices. -/
def intervalEmbed {n : ℕ} (a m : ℕ) (ha : 0 < a) (hb : a + m ≤ n) :
    Fin (m + 2) ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono
    (Fin.cases 0 (fun i : Fin (m + 1) => ⟨a + i.val, by have hi := i.isLt; lia⟩))
    (by
      intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (lt_irrefl _ hij).elim
        | succ j => change 0 < a + j.val; lia
      | succ i =>
        cases j using Fin.cases with
        | zero => exact (not_lt_of_ge (Fin.zero_le _) hij).elim
        | succ j =>
          change a + i.val < a + j.val
          have h : i.val < j.val := Fin.succ_lt_succ_iff.mp hij
          lia)

@[simp]
theorem intervalEmbed_zero {n a m : ℕ} (ha : 0 < a) (hb : a + m ≤ n) :
    intervalEmbed a m ha hb 0 = 0 := rfl

@[simp]
theorem intervalEmbed_succ_val {n a m : ℕ} (ha : 0 < a) (hb : a + m ≤ n)
    (i : Fin (m + 1)) : (intervalEmbed a m ha hb i.succ).val = a + i.val := rfl

@[simp]
theorem intervalEmbed_last_val {n a m : ℕ} (ha : 0 < a) (hb : a + m ≤ n) :
    (intervalEmbed a m ha hb (Fin.last (m + 1))).val = a + m := rfl

/-- Exact description of the vertices of the smaller complete diagram. -/
theorem intervalEmbed_range {n a m : ℕ} (ha : 0 < a) (hb : a + m ≤ n)
    (v : Fin (n + 1)) :
    (∃ u, intervalEmbed a m ha hb u = v) ↔
      v = 0 ∨ (a ≤ v.val ∧ v.val ≤ a + m) := by
  constructor
  · rintro ⟨u, rfl⟩
    cases u using Fin.cases with
    | zero => exact Or.inl rfl
    | succ u =>
      right
      change a ≤ a + u.val ∧ a + u.val ≤ a + m
      have hu := u.isLt
      constructor <;> lia
  · rintro (rfl | ⟨hlo, hhi⟩)
    · exact ⟨0, rfl⟩
    · let u : Fin (m + 1) := ⟨v.val - a, by lia⟩
      refine ⟨u.succ, Fin.ext ?_⟩
      change a + (v.val - a) = v.val
      lia

/-- Replacing the interval state cannot introduce a root edge below the interval. -/
theorem intervalExtend_no_low_head {n a m : ℕ} (ha : 0 < a) (hb : a + m ≤ n)
    (θ : Orientation (completeDiagram n))
    (hzero : ∀ v, 0 < v.val → v.val < a →
      ¬ (completeDiagram n).edgeData.selected θ.val 0 v)
    (α : Orientation (completeDiagram (m + 1)))
    (v : Fin (n + 1)) (hv : 0 < v.val) (hva : v.val < a) :
    ¬ (completeDiagram n).edgeData.selected
      (completeExtendAlong (intervalEmbed a m ha hb) θ α).val 0 v := by
  intro h
  rcases (completeExtendAlong_selected _ θ α 0 v).mp h with
    ⟨i, j, _, hj, _⟩ | ⟨_, h⟩
  · rcases (intervalEmbed_range ha hb v).mp ⟨j, hj⟩ with heq | hlo
    · have hval := congrArg Fin.val heq
      change v.val = 0 at hval
      lia
    · exact (not_le_of_gt hva) hlo.1
  · exact hzero v hv hva h

/-- The root and interval have the same cover tests before and after extension. -/
theorem intervalExtend_cover_iff {n a m : ℕ} (ha : 0 < a) (hb : a + m ≤ n)
    (θ : Orientation (completeDiagram n))
    (hzero : ∀ v, 0 < v.val → v.val < a →
      ¬ (completeDiagram n).edgeData.selected θ.val 0 v)
    (α : Orientation (completeDiagram (m + 1))) (u v : Fin (m + 2)) :
    Cover (completeExtendAlong (intervalEmbed a m ha hb) θ α)
        (intervalEmbed a m ha hb u) (intervalEmbed a m ha hb v) ↔ Cover α u v := by
  apply relationCover_iff_of_pathImage
  · exact pathImage_closed_of_zero_interval _ (intervalEmbed_range ha hb)
      (fun {_ _} h => (completeExtendAlong (intervalEmbed a m ha hb) θ α).selected_lt_of_forward
        (complete_forward n) h) ha (Nat.le_add_right a m)
      (intervalExtend_no_low_head ha hb θ hzero α)
  · exact fun u v => (completeExtendAlong_inside _ θ α u v).symm

/-- Every local flip path on `0,a,...,a+m` is actual globally with fixed exterior. -/
theorem interval_lift_reachable {n a m : ℕ} (ha : 0 < a) (hb : a + m ≤ n)
    (θ : Orientation (completeDiagram n))
    (hzero : ∀ v, 0 < v.val → v.val < a →
      ¬ (completeDiagram n).edgeData.selected θ.val 0 v)
    {α : Orientation (completeDiagram (m + 1))}
    (h : Relation.ReflTransGen (Flip (completeDiagram (m + 1)))
      (completeRestrictAlong (intervalEmbed a m ha hb) θ) α) :
    Relation.ReflTransGen (Flip (completeDiagram n)) θ
      (completeExtendAlong (intervalEmbed a m ha hb) θ α) :=
  complete_liftAlong_reachable _ θ (intervalExtend_cover_iff ha hb θ hzero) h

end

end VerticalStripLLT.Circular.DiagramProof
