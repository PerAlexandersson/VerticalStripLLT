import VerticalStripLLT.CyclicHessenberg.Kernel
import VerticalStripLLT.Polynomial
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Nodup

set_option autoImplicit false

/-! Color/tie-sorted boundary orders and their direct coloring enumerator. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V : Type*} [LinearOrder V]

/-- The decreasing list of vertices in one color fiber. -/
private def colorFiber {S : Finset V} {m : ℕ} (κ : S → Fin m) (c : Fin m) :
    List S :=
  (Finset.univ.filter fun v : S => κ v = c).sort (· ≥ ·)

private theorem mem_colorFiber {S : Finset V} {m : ℕ} (κ : S → Fin m)
    {c : Fin m} {v : S} : v ∈ colorFiber κ c ↔ κ v = c := by
  classical
  simp [colorFiber]

/-- Concatenate the decreasing color fibers in increasing color order. -/
private def sortedColorWord {S : Finset V} {m : ℕ} (κ : S → Fin m) : List S :=
  (List.ofFn (colorFiber κ)).flatten

private theorem sortedColorWord_nodup {S : Finset V} {m : ℕ} (κ : S → Fin m) :
    (sortedColorWord κ).Nodup := by
  classical
  rw [sortedColorWord, List.nodup_flatten]
  constructor
  · intro l hl
    obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hl
    exact Finset.sort_nodup _ _
  · rw [List.pairwise_ofFn]
    intro i j hij v hv hw
    have hvi : κ v = i := (mem_colorFiber κ).mp hv
    have hvj : κ v = j := (mem_colorFiber κ).mp hw
    exact (Fin.ne_of_lt hij) (hvi.symm.trans hvj)

private theorem mem_sortedColorWord {S : Finset V} {m : ℕ} (κ : S → Fin m)
    (v : S) : v ∈ sortedColorWord κ := by
  rw [sortedColorWord, List.mem_flatten]
  refine ⟨colorFiber κ (κ v), ?_, ?_⟩
  · exact List.mem_ofFn.mpr ⟨κ v, rfl⟩
  · exact (mem_colorFiber κ).mpr rfl

/-- List vertices by increasing color, breaking ties by decreasing vertex. -/
noncomputable def sortColorOrder {S : Finset V} {m : ℕ} (κ : S → Fin m) :
    Order S := by
  classical
  refine ⟨(sortedColorWord κ).map Subtype.val, ?_, ?_⟩
  · exact (sortedColorWord_nodup κ).map Subtype.val_injective
  · apply Finset.ext
    intro v
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨u, hu, huv⟩
      exact huv ▸ u.property
    · intro hv
      exact ⟨⟨v, hv⟩, mem_sortedColorWord κ ⟨v, hv⟩, rfl⟩

/-- The unique boundary order on an empty support. -/
def emptyOrder {V : Type*} [LinearOrder V] : Order (∅ : Finset V) :=
  ⟨[], by simp [IsOrder]⟩

private def emptyColoring {V : Type*} {m : ℕ} : (∅ : Finset V) → Fin m :=
  fun v => False.elim (Finset.notMem_empty v.val v.property)

/-- Sum a boundary functional over colorings in color/tie order. -/
noncomputable def orderColoringEnumerator {S : Finset V} (f : Order S → Q)
    (m : ℕ) : XPoly m :=
  ∑ κ : S → Fin m,
    MvPolynomial.C (f (sortColorOrder κ)) * ∏ v : S, MvPolynomial.X (κ v)

/-- The coloring enumerator attached to the diagonal of a finite kernel. -/
noncomputable def kernelColoringLLT {S : Finset V} (Z : Kernel Q S) (m : ℕ) :
    XPoly m :=
  orderColoringEnumerator (fun π => Z π π) m

/-- On empty support, the enumerator is the scalar at its unique boundary order. -/
theorem orderColoringEnumerator_empty {m : ℕ}
    (f : Order (∅ : Finset V) → Q) :
    orderColoringEnumerator f m = MvPolynomial.C (f emptyOrder) := by
  classical
  let : Unique ((∅ : Finset V) → Fin m) := {
    default := emptyColoring
    uniq := by
      intro κ
      funext v
      exact False.elim (Finset.notMem_empty v.val v.property) }
  have horder (κ : (∅ : Finset V) → Fin m) : sortColorOrder κ = emptyOrder :=
    Subsingleton.elim _ _
  simp [orderColoringEnumerator, horder]

/-- No coloring exists when the support is nonempty and the alphabet is empty. -/
theorem orderColoringEnumerator_zero_alphabet {S : Finset V}
    (f : Order S → Q) (hS : S.Nonempty) : orderColoringEnumerator f 0 = 0 := by
  classical
  rcases hS with ⟨v, hv⟩
  let : IsEmpty (S → Fin 0) := ⟨fun κ => Fin.elim0 (κ ⟨v, hv⟩)⟩
  simp [orderColoringEnumerator]

/-- The coloring enumerator is additive in its boundary functional. -/
theorem orderColoringEnumerator_add {S : Finset V} (f g : Order S → Q) (m : ℕ) :
    orderColoringEnumerator (fun π => f π + g π) m =
      orderColoringEnumerator f m + orderColoringEnumerator g m := by
  classical
  simp [orderColoringEnumerator, add_mul, Finset.sum_add_distrib]

/-- Scalar multiplication of the boundary functional becomes polynomial scalar
multiplication of its enumerator. -/
theorem orderColoringEnumerator_smul {S : Finset V} (a : Q) (f : Order S → Q)
    (m : ℕ) :
    orderColoringEnumerator (fun π => a * f π) m =
      MvPolynomial.C a * orderColoringEnumerator f m := by
  classical
  unfold orderColoringEnumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro κ hκ
  simp [map_mul, mul_assoc]

/-- The diagonal kernel enumerator has the corresponding empty-support value. -/
theorem kernelColoringLLT_empty {m : ℕ} (Z : Kernel Q (∅ : Finset V)) :
    kernelColoringLLT Z m = MvPolynomial.C (Z emptyOrder emptyOrder) := by
  exact orderColoringEnumerator_empty (m := m) (fun π => Z π π)

/-- The diagonal kernel enumerator vanishes for a nonempty support and no colors. -/
theorem kernelColoringLLT_zero_alphabet {S : Finset V} (Z : Kernel Q S)
    (hS : S.Nonempty) : kernelColoringLLT Z 0 = 0 := by
  exact orderColoringEnumerator_zero_alphabet (fun π => Z π π) hS

end VerticalStripLLT.CyclicHessenberg
