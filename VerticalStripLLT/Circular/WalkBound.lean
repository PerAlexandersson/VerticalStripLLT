import VerticalStripLLT.Circular.Diagram
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace VerticalStripLLT.Circular

/- Ported from the completed Aristotle candidate for project
8da2f9e8-2c92-4aaa-83a7-a88f6f36d257, task
bdd5052c-9aeb-45f2-b951-0455c14d11d6. -/

/-- Helper: along a walk, any strictly later vertex is reachable by a `TransGen` path. -/
theorem walk_transGen_of_lt {n k : ℕ} (R : Fin n → Fin n → Prop)
    (f : Fin (k + 1) → Fin n)
    (hstep : ∀ i : Fin k, R (f i.castSucc) (f i.succ)) :
    ∀ (d i : ℕ) (hi : i + d + 1 < k + 1),
      Relation.TransGen R (f ⟨i, by lia⟩) (f ⟨i + d + 1, hi⟩) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have h := hstep ⟨i, by lia⟩
    exact Relation.TransGen.single h
  | succ d ih =>
    intro i hi
    have h1 := ih i (by lia)
    have h2 := hstep ⟨i + d + 1, by lia⟩
    exact Relation.TransGen.tail h1 h2

/-- A directed walk in a finite acyclic graph never repeats a vertex. -/
theorem acyclic_walk_injective {n k : ℕ} (R : Fin n → Fin n → Prop)
    (hacyclic : ∀ v, ¬ Relation.TransGen R v v) (f : Fin (k + 1) → Fin n)
    (hstep : ∀ i : Fin k, R (f i.castSucc) (f i.succ)) :
    Function.Injective f := by
  have key : ∀ a b : Fin (k + 1), a.val < b.val → f a ≠ f b := by
    intro a b hab heq
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    simp only at hab
    obtain ⟨d, rfl⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by lia⟩
    have h := walk_transGen_of_lt R f hstep d a hb
    rw [heq] at h
    exact hacyclic _ h
  intro a b hab
  rcases lt_trichotomy a.val b.val with h | h | h
  · exact absurd hab (key a b h)
  · exact Fin.ext h
  · exact absurd hab.symm (key b a h)

/-- The projected path has at most n-1 edges. -/
theorem acyclic_walk_length_lt {n k : ℕ} (R : Fin n → Fin n → Prop)
    (hacyclic : ∀ v, ¬ Relation.TransGen R v v) (f : Fin (k + 1) → Fin n)
    (hstep : ∀ i : Fin k, R (f i.castSucc) (f i.succ)) : k < n := by
  have h := Fintype.card_le_of_injective f (acyclic_walk_injective R hacyclic f hstep)
  simp only [Fintype.card_fin] at h
  lia

/-- Helper: telescoping bound on a lifted walk. -/
theorem lifted_telescope {k : ℕ} (c : ℤ) (p : Fin (k + 1) → ℤ)
    (hbound : ∀ i : Fin k, p i.succ - p i.castSucc ≤ c) :
    ∀ (m : ℕ) (hm : m < k + 1), p ⟨m, hm⟩ - p 0 ≤ m * c := by
  intro m
  induction m with
  | zero => intro hm; simp
  | succ m ih =>
    intro hm
    have h1 := ih (by lia)
    have h2 := hbound ⟨m, by lia⟩
    have e1 : (Fin.succ ⟨m, by lia⟩ : Fin (k + 1)) = ⟨m + 1, hm⟩ := rfl
    have e2 : (Fin.castSucc ⟨m, by lia⟩ : Fin (k + 1)) = ⟨m, by lia⟩ := rfl
    rw [e1, e2] at h2
    push_cast
    linarith

/-- A lifted walk with steps at most n-1 has bounded total displacement.
This does not claim that it stays in one fundamental interval. -/
theorem acyclic_lifted_walk_span_le {n k : ℕ} (R : Fin n → Fin n → Prop)
    (hacyclic : ∀ v, ¬ Relation.TransGen R v v) (f : Fin (k + 1) → Fin n)
    (hstep : ∀ i : Fin k, R (f i.castSucc) (f i.succ))
    (p : Fin (k + 1) → ℤ)
    (hbound : ∀ i : Fin k, p i.succ - p i.castSucc ≤ (n - 1 : ℕ)) :
    p (Fin.last k) - p 0 ≤ ((n - 1 : ℕ) : ℤ) ^ 2 := by
  have hk := acyclic_walk_length_lt R hacyclic f hstep
  have h := lifted_telescope _ p hbound k (by lia)
  have e : (⟨k, by lia⟩ : Fin (k + 1)) = Fin.last k := rfl
  rw [e] at h
  have hk' : (k : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by exact_mod_cast (by lia : k ≤ n - 1)
  have hnn : (0 : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by positivity
  nlinarith

end VerticalStripLLT.Circular
