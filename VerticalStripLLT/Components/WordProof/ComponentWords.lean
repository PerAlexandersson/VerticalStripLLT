import VerticalStripLLT.Circular.ComponentSemantics
import VerticalStripLLT.Components.WordProof.WordRelations
import VerticalStripLLT.Components.WordProof.WordRank
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Full-word counts in the actual circular flip component and their linear extension.

The count is defined for every circular diagram. Descent through the four-word
relations still requires the ordinary forward-edge hypothesis and a flip bijection.
-/

namespace VerticalStripLLT.Components

noncomputable section

open Circular

/-- A full word lists every vertex exactly once, including the empty vertex set. -/
def fullWord {V : Type*} (w : List V) : Prop :=
  w.Nodup ∧ ∀ v, v ∈ w

theorem fullWord_perm_iff {V : Type*} {w w' : List V} (h : w.Perm w') :
    fullWord w ↔ fullWord w' := by
  simp only [fullWord, h.nodup_iff, h.mem_iff]

theorem fullWord_length {V : Type*} [Fintype V] {w : List V}
    (hw : fullWord w) : w.length = Fintype.card V := by
  classical
  have hs : w.toFinset = Finset.univ := by
    ext v
    simp [hw.2 v]
  rw [← List.toFinset_card_of_nodup hw.1, hs, Finset.card_univ]

@[simp]
theorem fullWord_nil_iff {V : Type*} : fullWord ([] : List V) ↔ IsEmpty V := by
  constructor
  · intro h
    exact ⟨fun v => List.not_mem_nil (h.2 v)⟩
  · intro h
    exact ⟨List.nodup_nil, fun v => (h.false v).elim⟩

variable {n : ℕ} {D : Diagram n}

/-- States in the complete component whose selected edges point right in the word. -/
def compatibleComponent (D : Diagram n) (θ : Circular.Orientation D) (w : List (Fin n)) :
    Finset (Circular.Orientation D) := by
  classical
  exact (flipComponent D θ).filter fun η => wordCompatible (D.edgeData.selected η.val) w

@[simp]
theorem mem_compatibleComponent (θ η : Circular.Orientation D) (w : List (Fin n)) :
    η ∈ compatibleComponent D θ w ↔
      η ∈ flipComponent D θ ∧ wordCompatible (D.edgeData.selected η.val) w := by
  classical
  simp [compatibleComponent]

/-- The integer component count, extended by zero off full permutations. -/
def componentWordCount (D : Diagram n) (θ : Circular.Orientation D) (w : List (Fin n)) : ℤ := by
  classical
  exact if fullWord w then (compatibleComponent D θ w).card else 0

theorem componentWordCount_of_full (θ : Circular.Orientation D) {w : List (Fin n)}
    (hw : fullWord w) :
    componentWordCount D θ w = (compatibleComponent D θ w).card := by
  simp [componentWordCount, hw]

theorem componentWordCount_of_not_full (θ : Circular.Orientation D) {w : List (Fin n)}
    (hw : ¬ fullWord w) : componentWordCount D θ w = 0 := by
  simp [componentWordCount, hw]

theorem componentWordCount_of_not_nodup (θ : Circular.Orientation D) {w : List (Fin n)}
    (hw : ¬ w.Nodup) : componentWordCount D θ w = 0 :=
  componentWordCount_of_not_full θ fun h => hw h.1

theorem componentWordCount_of_missing (θ : Circular.Orientation D) {w : List (Fin n)}
    {v : Fin n} (hv : v ∉ w) : componentWordCount D θ w = 0 :=
  componentWordCount_of_not_full θ fun h => hv (h.2 v)

theorem componentWordCount_of_length_ne (θ : Circular.Orientation D) {w : List (Fin n)}
    (hw : w.length ≠ n) : componentWordCount D θ w = 0 := by
  apply componentWordCount_of_not_full θ
  intro h
  exact hw (by simpa using fullWord_length h)

theorem componentWordCount_nonneg (θ : Circular.Orientation D) (w : List (Fin n)) :
    0 ≤ componentWordCount D θ w := by
  classical
  unfold componentWordCount
  split <;> positivity

theorem componentWordCount_eq_of_mem {θ η : Circular.Orientation D}
    (hη : η ∈ flipComponent D θ) (w : List (Fin n)) :
    componentWordCount D η w = componentWordCount D θ w := by
  simp only [componentWordCount, compatibleComponent, flipComponent_eq_of_mem hη]

/-- A contributing word gives a strict rank on every selected edge of that state. -/
theorem compatibleComponent_idxOf_lt (θ : Circular.Orientation D) {η : Circular.Orientation D}
    {w : List (Fin n)} (hw : fullWord w) (hη : η ∈ compatibleComponent D θ w)
    {u v : Fin n} (huv : D.edgeData.selected η.val u v) :
    w.idxOf u < w.idxOf v := by
  apply wordCompatible_idxOf_lt (D.edgeData.selected η.val) w
    (fun x hx => η.property.2 x (Relation.TransGen.single hx))
    (mem_compatibleComponent θ η w |>.mp hη).2 (hw.2 u) (hw.2 v) huv

/-- Pair integer word combinations with their actual component counts. -/
def componentWordLinear (D : Diagram n) (θ : Circular.Orientation D) :
    WordModule (Fin n) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (componentWordCount D θ)

@[simp]
theorem componentWordLinear_basisWord (θ : Circular.Orientation D) (w : List (Fin n)) :
    componentWordLinear D θ (basisWord w) = componentWordCount D θ w := by
  simp [componentWordLinear, basisWord]

theorem componentWordLinear_repeated (θ : Circular.Orientation D) {w : List (Fin n)}
    (hw : ¬ w.Nodup) : componentWordLinear D θ (basisWord w) = 0 := by
  rw [componentWordLinear_basisWord, componentWordCount_of_not_nodup θ hw]

end

end VerticalStripLLT.Components
