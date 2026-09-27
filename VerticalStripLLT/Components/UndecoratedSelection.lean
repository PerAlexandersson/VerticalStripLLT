import VerticalStripLLT.Circular.HRVPotential

/-!
# Preserving selected-edge semantics in an undecorated diagram

Move the strict edges into the selected orientation set while keeping the
same circular area sequence. The selected relation, integer-cover steps,
actual HRV map, and strict-coloring enumerator are unchanged. This file makes
no assertion about whole flip components.
-/

namespace VerticalStripLLT.Circular

open scoped Classical

noncomputable section

namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- The same natural circular graph with no distinguished strict edges. -/
def undecorated : Diagram n where
  area := D.area
  strict := ∅
  strict_corner := by
    intro e he
    simp at he

@[simp]
theorem undecorated_area : D.undecorated.area = D.area := rfl

@[simp]
theorem undecorated_strict : D.undecorated.strict = ∅ := rfl

@[simp]
theorem undecorated_normalEdges : D.undecorated.edgeData.normalEdges = Finset.univ := by
  change (Finset.univ \ ∅ : Finset (Edge D.area)) = Finset.univ
  exact Finset.sdiff_empty

/-- Strict and selected edges become one selected set in the undecorated graph. -/
theorem undecorated_selected (A : Finset (Edge D.area)) :
    D.undecorated.edgeData.selected (D.strict ∪ A) = D.edgeData.selected A := by
  funext u v
  change (∃ e ∈ (∅ : Finset (Edge D.area)) ∪ (D.strict ∪ A),
    e.tail = u ∧ e.head = v) = (∃ e ∈ D.strict ∪ A, e.tail = u ∧ e.head = v)
  rw [Finset.empty_union]

theorem undecorated_admissible_iff (A : Finset (Edge D.area)) :
    D.undecorated.edgeData.Admissible (D.strict ∪ A) ↔ D.edgeData.Admissible A := by
  unfold EdgeData.Admissible
  rw [D.undecorated_selected A]

/-- The same integer-cover relation is retained, with the same natural lengths. -/
theorem undecorated_liftStep (A : Finset (Edge D.area)) :
    D.undecorated.liftStep (D.strict ∪ A) = D.liftStep A := by
  funext z w
  change (∃ e ∈ (∅ : Finset (Edge D.area)) ∪ (D.strict ∪ A),
    D.residue z = e.tail ∧ w = z + (e.length.val : ℤ)) =
    (∃ e ∈ D.strict ∪ A, D.residue z = e.tail ∧ w = z + (e.length.val : ℤ))
  rw [Finset.empty_union]

/-- The actual finite strict-coloring polynomial only sees the full selected set. -/
theorem undecorated_strictOrderEnumerator (A : Finset (Edge D.area)) (m : ℕ) :
    D.undecorated.edgeData.strictOrderEnumerator (D.strict ∪ A) m =
      D.edgeData.strictOrderEnumerator A m := by
  unfold EdgeData.strictOrderEnumerator
  apply Finset.sum_congr rfl
  intro c _
  have hc : (∀ e ∈ D.undecorated.edgeData.strict ∪ (D.strict ∪ A),
      c (D.undecorated.edgeData.tail e) < c (D.undecorated.edgeData.head e)) ↔
      (∀ e ∈ D.edgeData.strict ∪ A, c (D.edgeData.tail e) < c (D.edgeData.head e)) := by
    change (∀ e ∈ (∅ : Finset (Edge D.area)) ∪ (D.strict ∪ A), c e.tail < c e.head) ↔
      (∀ e ∈ D.strict ∪ A, c e.tail < c e.head)
    rw [Finset.empty_union]
  simp only [hc]
  split_ifs <;> rfl

end Diagram

namespace Orientation

variable {n : ℕ} {D : Diagram n}

/-- Retain every originally selected edge as a normal selected edge of the same area. -/
def toUndecorated (θ : Orientation D) : Orientation D.undecorated := by
  refine ⟨D.strict ∪ θ.val, ?_, ?_⟩
  · rw [D.undecorated_normalEdges]
    exact Finset.subset_univ _
  · exact (D.undecorated_admissible_iff θ.val).mpr θ.property.2

@[simp]
theorem toUndecorated_val (θ : Orientation D) :
    θ.toUndecorated.val = D.strict ∪ θ.val := rfl

theorem toUndecorated_selected (θ : Orientation D) :
    D.undecorated.edgeData.selected θ.toUndecorated.val =
      D.edgeData.selected θ.val := D.undecorated_selected θ.val

theorem toUndecorated_liftStep (θ : Orientation D) :
    D.undecorated.liftStep θ.toUndecorated.val = D.liftStep θ.val :=
  D.undecorated_liftStep θ.val

/-- The entire highest-reachable integer map is unchanged. -/
@[simp]
theorem toUndecorated_liftedHRV (θ : Orientation D) (z : ℤ) :
    θ.toUndecorated.liftedHRV z = θ.liftedHRV z := by
  apply θ.liftedHRV_eq_of_potential θ.toUndecorated
  · intro x y h
    apply Relation.ReflTransGen.single
    rwa [θ.toUndecorated_liftStep]
  · intro x y h
    apply θ.liftedHRV_le_of_step
    rwa [θ.toUndecorated_liftStep] at h

@[simp]
theorem toUndecorated_hrv (θ : Orientation D) : θ.toUndecorated.hrv = θ.hrv := by
  funext u
  unfold hrv
  rw [θ.toUndecorated_liftedHRV]
  rfl

@[simp]
theorem toUndecorated_hrvMonomial (θ : Orientation D) :
    θ.toUndecorated.hrvMonomial = θ.hrvMonomial := by
  unfold hrvMonomial
  rw [θ.toUndecorated_hrv]

@[simp]
theorem toUndecorated_strictOrderEnumerator (θ : Orientation D) (m : ℕ) :
    D.undecorated.edgeData.strictOrderEnumerator θ.toUndecorated.val m =
      D.edgeData.strictOrderEnumerator θ.val m :=
  D.undecorated_strictOrderEnumerator θ.val m

end Orientation

end

end VerticalStripLLT.Circular
