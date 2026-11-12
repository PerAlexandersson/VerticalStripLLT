import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.List.Zip

set_option autoImplicit false

/-! Structural compatibility of composition splitting with list operations. -/

namespace List

variable {α β γ : Type*}
variable {n : ℕ}

theorem splitWrtCompositionAux_map (l : List α) (ns : List ℕ) (f : α → β) :
    (l.map f).splitWrtCompositionAux ns =
      (l.splitWrtCompositionAux ns).map (List.map f) := by
  induction ns generalizing l with
  | nil => simp [splitWrtCompositionAux]
  | cons n ns ih =>
      simp only [splitWrtCompositionAux_cons, List.map_cons, ← List.map_take,
        ← List.map_drop, ih]

/-- Mapping a list commutes with splitting it into composition blocks. -/
theorem splitWrtComposition_map (l : List α) (c : Composition n) (f : α → β) :
    (l.map f).splitWrtComposition c =
      (l.splitWrtComposition c).map (List.map f) := by
  simpa [splitWrtComposition] using splitWrtCompositionAux_map l c.blocks f

theorem splitWrtCompositionAux_zip (l₁ : List α) (l₂ : List β) (ns : List ℕ) :
    (l₁.zip l₂).splitWrtCompositionAux ns =
      (l₁.splitWrtCompositionAux ns).zipWith List.zip (l₂.splitWrtCompositionAux ns) := by
  induction ns generalizing l₁ l₂ with
  | nil => simp [splitWrtCompositionAux]
  | cons n ns ih =>
      simp only [splitWrtCompositionAux_cons, List.zipWith_cons_cons]
      change List.take n (List.zipWith Prod.mk l₁ l₂) ::
        (List.drop n (List.zipWith Prod.mk l₁ l₂)).splitWrtCompositionAux ns = _
      rw [List.take_zipWith, List.drop_zipWith]
      exact congrArg (List.cons ((l₁.take n).zip (l₂.take n))) (ih (l₁.drop n) (l₂.drop n))

/-- Splitting a zipped pair of lists produces the corresponding zipped blocks. -/
theorem splitWrtComposition_zip (l₁ : List α) (l₂ : List β) (c : Composition n) :
    (l₁.zip l₂).splitWrtComposition c =
      (l₁.splitWrtComposition c).zipWith List.zip (l₂.splitWrtComposition c) := by
  simpa [splitWrtComposition] using splitWrtCompositionAux_zip l₁ l₂ c.blocks

/-- Reconstruct the blocks from their flattening and their prescribed block lengths. -/
theorem splitWrtComposition_eq_of_flatten_eq {l : List α} {k : ℕ}
    (c : Composition k) (hlen : l.length = k) (B : List (List α))
    (hflat : B.flatten = l) (hblocks : B.map List.length = c.blocks) :
    l.splitWrtComposition c = B := by
  have hsize : B.flatten.length = k := by rw [hflat, hlen]
  cases hsize
  rw [← hflat]
  exact List.splitWrtComposition_flatten B c hblocks

end List
