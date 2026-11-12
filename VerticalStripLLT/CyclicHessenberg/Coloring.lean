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

/-- The color/tie order: colors increase, and equal colors reverse vertices. -/
def fiberColorPrecedes {S : Finset V} {m : ℕ} (κ : S → Fin m) (a b : S) : Prop :=
  κ a < κ b ∨ (κ a = κ b ∧ b < a)

/-- Concatenate the decreasing color fibers in increasing color order. -/
def sortedColorWord {S : Finset V} {m : ℕ} (κ : S → Fin m) : List S :=
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

private theorem colorFiber_pairwise {S : Finset V} {m : ℕ} (κ : S → Fin m)
    (c : Fin m) : (colorFiber κ c).Pairwise (fiberColorPrecedes κ) := by
  classical
  rw [List.pairwise_iff_get]
  intro i j hij
  let l := colorFiber κ c
  have hsorted : l.Pairwise (· ≥ ·) := Finset.pairwise_sort _ _
  have hdesc : l.get j ≤ l.get i := hsorted.rel_get_of_lt hij
  have hne : l.get i ≠ l.get j := by
    intro heq
    exact (Fin.ne_of_lt hij) ((Finset.sort_nodup _ _).injective_get heq)
  have hi : κ (l.get i) = c := (mem_colorFiber κ).mp (List.get_mem l i)
  have hj : κ (l.get j) = c := (mem_colorFiber κ).mp (List.get_mem l j)
  exact Or.inr ⟨hi.trans hj.symm, lt_of_le_of_ne hdesc hne.symm⟩

/-- The color/tie-sorted word is pairwise ordered by `fiberColorPrecedes`. -/
theorem sortedColorWord_pairwise {S : Finset V} {m : ℕ} (κ : S → Fin m) :
    (sortedColorWord κ).Pairwise (fiberColorPrecedes κ) := by
  classical
  rw [sortedColorWord, List.pairwise_flatten]
  constructor
  · intro l hl
    obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hl
    exact colorFiber_pairwise κ c
  · rw [List.pairwise_ofFn]
    intro i j hij x hx y hy
    have hxi : κ x = i := (mem_colorFiber κ).mp hx
    have hyj : κ y = j := (mem_colorFiber κ).mp hy
    exact Or.inl (by simpa [hxi, hyj] using hij)

/-- Compare ambient vertices using their canonical membership in a support. -/
def colorPrecedesOn {S : Finset V} {m : ℕ} (κ : S → Fin m) (a b : V) : Prop :=
  ∃ ha : a ∈ S, ∃ hb : b ∈ S, fiberColorPrecedes κ ⟨a, ha⟩ ⟨b, hb⟩

/-- A boundary order is color/tie sorted when its list is pairwise ordered. -/
def IsColorSortedOrder {S : Finset V} {m : ℕ} (κ : S → Fin m) (l : Order S) : Prop :=
  l.val.Pairwise (colorPrecedesOn κ)

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

/-- The constructed boundary order satisfies the color/tie ordering. -/
theorem sortColorOrder_colorSorted {S : Finset V} {m : ℕ} (κ : S → Fin m) :
    IsColorSortedOrder κ (sortColorOrder κ) := by
  change ((sortedColorWord κ).map Subtype.val).Pairwise (colorPrecedesOn κ)
  rw [List.pairwise_map]
  exact (sortedColorWord_pairwise κ).imp fun a b hab =>
    ⟨a.property, b.property, hab⟩

/-- Mutually preceding vertices cannot occur in the strict color/tie order. -/
private theorem fiberColorPrecedes_asymm {S : Finset V} {m : ℕ} (κ : S → Fin m)
    (a b : S) (hab : fiberColorPrecedes κ a b) (hba : fiberColorPrecedes κ b a) : False := by
  rcases hab with hab | ⟨hab, hab'⟩
  · rcases hba with hba | ⟨hba, hba'⟩
    · exact (lt_asymm hab hba).elim
    · rw [hba] at hab
      exact (lt_irrefl _ hab).elim
  · rcases hba with hba | ⟨hba, hba'⟩
    · rw [← hab] at hba
      exact (lt_irrefl _ hba).elim
    · exact (lt_asymm hab' hba').elim

private theorem colorPrecedesOn_asymm {S : Finset V} {m : ℕ} (κ : S → Fin m)
    {a b : V} (hab : colorPrecedesOn κ a b) (hba : colorPrecedesOn κ b a) : False := by
  rcases hab with ⟨ha, hb, hab⟩
  rcases hba with ⟨hb', ha', hba⟩
  have hbEq : (⟨b, hb'⟩ : S) = ⟨b, hb⟩ := Subtype.ext rfl
  have haEq : (⟨a, ha'⟩ : S) = ⟨a, ha⟩ := Subtype.ext rfl
  rw [hbEq, haEq] at hba
  exact fiberColorPrecedes_asymm κ _ _ hab hba

/-- The constructed boundary order has the stated inequality at every pair of
ordered positions. -/
theorem sortColorOrder_orderEquiv_precedes {S : Finset V} {m : ℕ}
    (κ : S → Fin m) {i j : Fin S.card} (hij : i < j) :
    fiberColorPrecedes κ (orderEquiv (sortColorOrder κ) i)
      (orderEquiv (sortColorOrder κ) j) := by
  let l := sortColorOrder κ
  let i' : Fin l.val.length := Fin.cast (length_order l).symm i
  let j' : Fin l.val.length := Fin.cast (length_order l).symm j
  have hlt : i' < j' := by
    apply Fin.lt_def.mpr
    simpa [i', j', Fin.cast] using Fin.lt_def.mp hij
  have hpair := (sortColorOrder_colorSorted κ).rel_get_of_lt hlt
  rcases hpair with ⟨hi, hj, hpre⟩
  have hei : orderEquiv l i = ⟨l.val.get i', hi⟩ := by
    apply Subtype.ext
    simpa [i'] using orderEquiv_apply l i
  have hej : orderEquiv l j = ⟨l.val.get j', hj⟩ := by
    apply Subtype.ext
    simpa [j'] using orderEquiv_apply l j
  simpa only [hei, hej] using hpre

/-- A boundary order with the color/tie pairwise property is unique. -/
theorem sortColorOrder_unique {S : Finset V} {m : ℕ} (κ : S → Fin m)
    (l : Order S) (hl : IsColorSortedOrder κ l) : l = sortColorOrder κ := by
  have hp : l.val.Perm (sortColorOrder κ).val :=
    List.perm_of_nodup_nodup_toFinset_eq l.property.1
      (sortColorOrder κ).property.1
      (l.property.2.trans (sortColorOrder κ).property.2.symm)
  letI : Std.Antisymm (colorPrecedesOn κ) :=
    ⟨fun a b hab hba => False.elim (colorPrecedesOn_asymm κ hab hba)⟩
  apply Subtype.ext
  exact List.Perm.eq_of_pairwise' hl (sortColorOrder_colorSorted κ) hp

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
