import VerticalStripLLT.CyclicHessenberg.BoundaryOrder
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

/-! Scalar boundary exchange with independently fixed row and column contexts. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V R : Type*} [LinearOrder V]

/-- A finite transfer matrix on orders of one named support. -/
abbrev Kernel (R : Type*) (S : Finset V) := Matrix (Order S) (Order S) R

/-- Evaluate a finite kernel on lists, assigning zero to invalid boundary orders. -/
noncomputable def kernelEntry [Zero R] {S : Finset V} (Z : Kernel R S)
    (l t : List V) : R := by
  classical
  exact if hl : IsOrder S l then
    if ht : IsOrder S t then Z ⟨l, hl⟩ ⟨t, ht⟩ else 0
  else 0

@[simp] theorem kernelEntry_order [Zero R] {S : Finset V} (Z : Kernel R S)
    (l t : Order S) : kernelEntry Z l.val t.val = Z l t := by
  simp [kernelEntry, l.property, t.property]

/-- Restrict to the suffix support, fixing independently ordered prefixes. -/
def prefixKernel {A B : Finset V} (hd : Disjoint A B) (Z : Kernel R (A ∪ B))
    (p p' : Order A) : Kernel R B :=
  fun l t => Z (appendOrder hd p l) (appendOrder hd p' t)

/-- Restrict to the prefix support, fixing independently ordered suffixes. -/
def suffixKernel {A B : Finset V} (hd : Disjoint A B) (Z : Kernel R (A ∪ B))
    (s s' : Order B) : Kernel R A :=
  fun l t => Z (appendOrder hd l s) (appendOrder hd t s')

theorem kernelEntry_prefixKernel [Zero R] {A B : Finset V} (hd : Disjoint A B)
    (Z : Kernel R (A ∪ B)) (p p' : Order A) (l t : List V) :
    kernelEntry (prefixKernel hd Z p p') l t =
      kernelEntry Z (p.val ++ l) (p'.val ++ t) := by
  classical
  have hl := isOrder_append_left_iff (l := l) p.property hd
  have ht := isOrder_append_left_iff (l := t) p'.property hd
  by_cases h₁ : IsOrder B l <;> by_cases h₂ : IsOrder B t
  all_goals simp [kernelEntry, prefixKernel, appendOrder, hl, ht, h₁, h₂]

theorem kernelEntry_suffixKernel [Zero R] {A B : Finset V} (hd : Disjoint A B)
    (Z : Kernel R (A ∪ B)) (s s' : Order B) (l t : List V) :
    kernelEntry (suffixKernel hd Z s s') l t =
      kernelEntry Z (l ++ s.val) (t ++ s'.val) := by
  classical
  have hl := isOrder_append_right_iff (l := l) s.property hd
  have ht := isOrder_append_right_iff (l := t) s'.property hd
  by_cases h₁ : IsOrder A l <;> by_cases h₂ : IsOrder A t
  all_goals simp [kernelEntry, suffixKernel, appendOrder, hl, ht, h₁, h₂]

section Semiring

variable [CommSemiring R]

/-- The two scalar exchange laws on lists. Equal prefix lengths mean the exchanged
pairs occupy the same positions; the two exterior contexts may otherwise differ. -/
def ListExchangeCompatible (q : R) (Z : List V → List V → R) : Prop :=
  ∀ (ρ σ ρ' σ' : List V) (a b c d : V),
    ρ.length = ρ'.length → a < b → c < d →
      Z (ρ ++ [a, b] ++ σ) (ρ' ++ [d, c] ++ σ') =
          (1 + q) * Z (ρ ++ [b, a] ++ σ) (ρ' ++ [c, d] ++ σ') ∧
      Z (ρ ++ [a, b] ++ σ) (ρ' ++ [c, d] ++ σ') =
          Z (ρ ++ [b, a] ++ σ) (ρ' ++ [d, c] ++ σ') +
            q * Z (ρ ++ [b, a] ++ σ) (ρ' ++ [c, d] ++ σ')

/-- Exchange compatibility of a finite kernel, using its zero extension. -/
def ExchangeCompatible (q : R) {S : Finset V} (Z : Kernel R S) : Prop :=
  ListExchangeCompatible q (kernelEntry Z)

namespace ListExchangeCompatible

theorem zero (q : R) :
    ListExchangeCompatible (V := V) q (fun _ _ => (0 : R)) := by
  intro ρ σ ρ' σ' a b c d hlen hab hcd
  simp

theorem add {q : R} {Z W : List V → List V → R}
    (hZ : ListExchangeCompatible q Z) (hW : ListExchangeCompatible q W) :
    ListExchangeCompatible q (fun l t => Z l t + W l t) := by
  intro ρ σ ρ' σ' a b c d hlen hab hcd
  obtain ⟨hZ₁, hZ₂⟩ := hZ ρ σ ρ' σ' a b c d hlen hab hcd
  obtain ⟨hW₁, hW₂⟩ := hW ρ σ ρ' σ' a b c d hlen hab hcd
  dsimp only
  constructor
  · rw [hZ₁, hW₁, mul_add]
  · rw [hZ₂, hW₂, mul_add]
    ring

theorem smul {q : R} {Z : List V → List V → R}
    (hZ : ListExchangeCompatible q Z) (s : R) :
    ListExchangeCompatible q (fun l t => s * Z l t) := by
  intro ρ σ ρ' σ' a b c d hlen hab hcd
  obtain ⟨h₁, h₂⟩ := hZ ρ σ ρ' σ' a b c d hlen hab hcd
  dsimp only
  constructor
  · rw [h₁]
    ring
  · rw [h₂]
    ring

/-- Fix different row and column prefixes of equal length. -/
theorem prefixLists {q : R} {Z : List V → List V → R}
    (hZ : ListExchangeCompatible q Z) (p p' : List V)
    (hp : p.length = p'.length) :
    ListExchangeCompatible q (fun l t => Z (p ++ l) (p' ++ t)) := by
  intro ρ σ ρ' σ' a b c d hlen hab hcd
  have h := hZ (p ++ ρ) σ (p' ++ ρ') σ' a b c d
    (by simp [hp, hlen]) hab hcd
  simpa only [List.append_assoc] using h

/-- Fix different row and column suffixes. The exchange position is unchanged. -/
theorem suffix {q : R} {Z : List V → List V → R}
    (hZ : ListExchangeCompatible q Z) (s s' : List V) :
    ListExchangeCompatible q (fun l t => Z (l ++ s) (t ++ s')) := by
  intro ρ σ ρ' σ' a b c d hlen hab hcd
  have h := hZ ρ (σ ++ s) ρ' (σ' ++ s') a b c d hlen hab hcd
  simpa only [List.append_assoc] using h

/-- Restrict inside arbitrary independently fixed boundary contexts. -/
theorem context {q : R} {Z : List V → List V → R}
    (hZ : ListExchangeCompatible q Z) (p p' s s' : List V)
    (hp : p.length = p'.length) :
    ListExchangeCompatible q (fun l t => Z (p ++ l ++ s) (p' ++ t ++ s')) := by
  exact (hZ.suffix s s').prefixLists p p' hp

theorem map {T : Type*} [CommSemiring T] {q : R} {Z : List V → List V → R}
    (hZ : ListExchangeCompatible q Z) (f : R →+* T) :
    ListExchangeCompatible (f q) (fun l t => f (Z l t)) := by
  intro ρ σ ρ' σ' a b c d hlen hab hcd
  obtain ⟨h₁, h₂⟩ := hZ ρ σ ρ' σ' a b c d hlen hab hcd
  exact ⟨by simpa using congrArg f h₁, by simpa using congrArg f h₂⟩

theorem sum {ι : Type*} (s : Finset ι) {q : R}
    (Z : ι → List V → List V → R)
    (hZ : ∀ i ∈ s, ListExchangeCompatible q (Z i)) :
    ListExchangeCompatible q (fun l t => ∑ i ∈ s, Z i l t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero (V := V) q
  | @insert i s hi ih =>
    have h₁ := hZ i (Finset.mem_insert_self i s)
    have h₂ := ih (fun j hj => hZ j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using h₁.add h₂

end ListExchangeCompatible

/-- Restrict a compatible list function to genuine orders and zero-extend it again. -/
theorem ListExchangeCompatible.toKernel {q : R} {Z : List V → List V → R}
    (hZ : ListExchangeCompatible q Z) (S : Finset V) :
    ExchangeCompatible q (fun π τ : Order S => Z π.val τ.val) := by
  classical
  intro ρ σ ρ' σ' a b c d hlen hab hcd
  by_cases hl : IsOrder S (ρ ++ [a, b] ++ σ)
  · have hl' := isOrder_swapAdjacent ρ σ a b hl
    by_cases ht : IsOrder S (ρ' ++ [c, d] ++ σ')
    · have ht' := isOrder_swapAdjacent ρ' σ' c d ht
      simpa only [kernelEntry, dite_eq_left hl, dite_eq_left hl', dite_eq_left ht,
        dite_eq_left ht'] using hZ ρ σ ρ' σ' a b c d hlen hab hcd
    · have ht' : ¬ IsOrder S (ρ' ++ [d, c] ++ σ') :=
        fun hh => ht (isOrder_swapAdjacent ρ' σ' d c hh)
      simp only [kernelEntry, dite_eq_left hl, dite_eq_left hl', dite_eq_right ht,
        dite_eq_right ht', mul_zero, add_zero, and_self]
  · have hl' : ¬ IsOrder S (ρ ++ [b, a] ++ σ) :=
      fun hh => hl (isOrder_swapAdjacent ρ σ b a hh)
    simp only [kernelEntry, dite_eq_right hl, dite_eq_right hl', mul_zero, add_zero, and_self]

theorem kernelEntry_map {T : Type*} [CommSemiring T] (f : R →+* T)
    {S : Finset V} (Z : Kernel R S) (l t : List V) :
    kernelEntry (fun π τ => f (Z π τ)) l t = f (kernelEntry Z l t) := by
  classical
  by_cases hl : IsOrder S l <;> by_cases ht : IsOrder S t
  all_goals simp [kernelEntry, hl, ht]

theorem ExchangeCompatible.map {T : Type*} [CommSemiring T] {q : R}
    {S : Finset V} {Z : Kernel R S} (hZ : ExchangeCompatible q Z) (f : R →+* T) :
    ExchangeCompatible (f q) (fun π τ => f (Z π τ)) := by
  have heq : kernelEntry (fun π τ => f (Z π τ)) = fun l t => f (kernelEntry Z l t) := by
    funext l t
    exact kernelEntry_map f Z l t
  rw [ExchangeCompatible, heq]
  exact ListExchangeCompatible.map hZ f

/-- Unequal fixed prefixes preserve all exchanges on the retained support. -/
theorem ExchangeCompatible.prefixKernel {q : R} {A B : Finset V}
    {Z : Kernel R (A ∪ B)} (hZ : ExchangeCompatible q Z)
    (hd : Disjoint A B) (p p' : Order A) :
    ExchangeCompatible q (prefixKernel hd Z p p') := by
  have heq : kernelEntry (CyclicHessenberg.prefixKernel hd Z p p') =
      fun l t => kernelEntry Z (p.val ++ l) (p'.val ++ t) := by
    funext l t
    exact kernelEntry_prefixKernel hd Z p p' l t
  rw [ExchangeCompatible, heq]
  exact ListExchangeCompatible.prefixLists hZ p.val p'.val (by simp)

/-- Unequal fixed suffixes preserve all exchanges on the retained support. -/
theorem ExchangeCompatible.suffixKernel {q : R} {A B : Finset V}
    {Z : Kernel R (A ∪ B)} (hZ : ExchangeCompatible q Z)
    (hd : Disjoint A B) (s s' : Order B) :
    ExchangeCompatible q (suffixKernel hd Z s s') := by
  have heq : kernelEntry (CyclicHessenberg.suffixKernel hd Z s s') =
      fun l t => kernelEntry Z (l ++ s.val) (t ++ s'.val) := by
    funext l t
    exact kernelEntry_suffixKernel hd Z s s' l t
  rw [ExchangeCompatible, heq]
  exact ListExchangeCompatible.suffix hZ s.val s'.val

/-- The four-term relation for a functional, in every fixed exterior context. -/
def ContextualBalance (f : List V → R) : Prop :=
  ∀ (ρ σ : List V) (a b c : V), a < b → b < c →
    f (ρ ++ [a, c, b] ++ σ) + f (ρ ++ [b, c, a] ++ σ) =
      f (ρ ++ [c, a, b] ++ σ) + f (ρ ++ [b, a, c] ++ σ)

/-- Four scalar exchange identities give the contextual diagonal relation. -/
theorem ListExchangeCompatible.diagonal_contextualBalance {q : R}
    {Z : List V → List V → R} (hZ : ListExchangeCompatible q Z) :
    ContextualBalance (fun l => Z l l) := by
  intro ρ σ a b c hab hbc
  have hac := lt_trans hab hbc
  have h₁ := (hZ ρ (b :: σ) ρ (b :: σ) a c a c rfl hac hac).2
  have h₂ := (hZ (ρ ++ [b]) σ (ρ ++ [b]) σ a c a c rfl hac hac).2
  have h₃ := (hZ (ρ ++ [c]) σ (ρ ++ [a]) σ a b b c
    (by simp) hab hbc).1
  have h₄ := (hZ ρ (a :: σ) ρ (c :: σ) b c a b rfl hbc hab).1
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h₁ h₂ h₃ h₄ ⊢
  rw [h₁, h₂, h₃, h₄]
  ring

theorem ExchangeCompatible.diagonal_contextualBalance {q : R} {S : Finset V}
    {Z : Kernel R S} (hZ : ExchangeCompatible q Z) :
    ContextualBalance (fun l => kernelEntry Z l l) :=
  ListExchangeCompatible.diagonal_contextualBalance hZ

end Semiring

section Ring

variable [CommRing R]

theorem ListExchangeCompatible.sub {q : R} {Z W : List V → List V → R}
    (hZ : ListExchangeCompatible q Z) (hW : ListExchangeCompatible q W) :
    ListExchangeCompatible q (fun l t => Z l t - W l t) := by
  intro ρ σ ρ' σ' a b c d hlen hab hcd
  obtain ⟨hZ₁, hZ₂⟩ := hZ ρ σ ρ' σ' a b c d hlen hab hcd
  obtain ⟨hW₁, hW₂⟩ := hW ρ σ ρ' σ' a b c d hlen hab hcd
  dsimp only
  constructor
  · rw [hZ₁, hW₁, mul_sub]
  · rw [hZ₂, hW₂, mul_sub]
    ring

/-- The signed intermediate kernel in the minimum-deletion induction remains compatible. -/
theorem ListExchangeCompatible.minimumDifference {q : R}
    {Z : List V → List V → R} (hZ : ListExchangeCompatible q Z)
    (a : V) (π τ : List V) :
    ListExchangeCompatible q (fun l t =>
      Z (a :: l ++ π) (a :: t ++ τ) - Z (l ++ [a] ++ π) (t ++ [a] ++ τ)) := by
  have hleft := (hZ.suffix π τ).prefixLists [a] [a] rfl
  have hright := hZ.suffix ([a] ++ π) ([a] ++ τ)
  simpa only [List.cons_append, List.nil_append, List.append_assoc] using hleft.sub hright

end Ring

end VerticalStripLLT.CyclicHessenberg
