import VerticalStripLLT.CyclicHessenberg.Kernel
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Positive residual kernels and the simultaneous minimum slide. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V R : Type*} [LinearOrder V]

section Semiring

variable [CommSemiring R]

/-- The positive residual is a sum of crossed entries, defined before its signed identity.
Applications require `r ∈ U` and that `r` is the largest remaining vertex. -/
noncomputable def rootDeletion (q : R) (Z : List V → List V → R)
    (U : Finset V) (r : V) (π τ : List V) : R :=
  q ^ (U.card - 1) * ∑ σ : Order (U.erase r),
    Z ((r :: σ.val) ++ π) ((σ.val ++ [r]) ++ τ)

/-- Every crossed summand fixes prefixes of equal length, although their orders differ. -/
theorem rootDeletion_exchangeCompatible {q : R} {Z : List V → List V → R}
    (hZ : ListExchangeCompatible q Z) (U : Finset V) (r : V) :
    ListExchangeCompatible q (rootDeletion q Z U r) := by
  classical
  apply ListExchangeCompatible.smul
  apply ListExchangeCompatible.sum
  intro σ hσ
  exact hZ.prefixLists (r :: σ.val) (σ.val ++ [r]) (by simp)

theorem rootDeletion_map {T : Type*} [CommSemiring T] (f : R →+* T)
    (q : R) (Z : List V → List V → R) (U : Finset V) (r : V) (π τ : List V) :
    f (rootDeletion q Z U r π τ) =
      rootDeletion (f q) (fun l t => f (Z l t)) U r π τ := by
  classical
  simp [rootDeletion]

/-- The crossed entries encountered while moving `a` simultaneously along both lists. -/
def minimumSlideSum (Z : List V → List V → R) (a : V) (π τ : List V) :
    List V → List V → List V → List V → R
  | ρ, ρ', x :: xs, y :: ys =>
    Z (ρ ++ x :: a :: xs ++ π) (ρ' ++ a :: y :: ys ++ τ) +
      minimumSlideSum Z a π τ (ρ ++ [x]) (ρ' ++ [y]) xs ys
  | _, _, _, _ => 0

/-- Each step is the second exchange law. The fixed row and column suffixes are arbitrary. -/
theorem minimumSlide {q : R} {Z : List V → List V → R}
    (hZ : ListExchangeCompatible q Z) (a : V) (π τ ρ ρ' xs ys : List V)
    (hρ : ρ.length = ρ'.length) (hlen : xs.length = ys.length)
    (hxs : ∀ x ∈ xs, a < x) (hys : ∀ y ∈ ys, a < y) :
    Z (ρ ++ a :: xs ++ π) (ρ' ++ a :: ys ++ τ) =
      Z (ρ ++ xs ++ [a] ++ π) (ρ' ++ ys ++ [a] ++ τ) +
        q * minimumSlideSum Z a π τ ρ ρ' xs ys := by
  induction xs generalizing ys ρ ρ' with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    simp [minimumSlideSum]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hax := hxs x (by simp)
      have hay := hys y (by simp)
      have hstep := (hZ ρ (xs ++ π) ρ' (ys ++ τ) a x a y hρ hax hay).2
      have htail := ih (ys := ys) (ρ := ρ ++ [x]) (ρ' := ρ' ++ [y])
        (by simp [hρ]) (by simpa using hlen)
        (fun z hz => hxs z (by simp [hz])) (fun z hz => hys z (by simp [hz]))
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hstep htail ⊢
      rw [hstep, htail]
      simp only [minimumSlideSum, List.append_assoc, List.cons_append]
      ring

/-- Index the crossed entries by the position of the moving minimum. -/
theorem minimumSlideSum_eq_sum (Z : List V → List V → R)
    (a : V) (π τ ρ ρ' xs ys : List V) (hlen : xs.length = ys.length) :
    minimumSlideSum Z a π τ ρ ρ' xs ys =
      ∑ i ∈ Finset.range xs.length,
        Z (ρ ++ xs.take (i + 1) ++ a :: xs.drop (i + 1) ++ π)
          (ρ' ++ ys.take i ++ a :: ys.drop i ++ τ) := by
  induction xs generalizing ys ρ ρ' with
  | nil => simp [minimumSlideSum]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      rw [minimumSlideSum, List.length_cons, Finset.sum_range_succ']
      rw [ih (ys := ys) (ρ := ρ ++ [x]) (ρ' := ρ' ++ [y]) (by simpa using hlen)]
      simp only [List.take_zero, List.drop_zero, List.take_succ_cons, List.drop_succ_cons,
        List.append_nil, List.nil_append, List.cons_append, List.append_assoc]
      exact add_comm _ _

/-- The minimum slide for a cyclically rotated pair is precisely a sum over insertion positions. -/
theorem minimumSlide_cycle {q : R} {Z : List V → List V → R}
    (hZ : ListExchangeCompatible q Z) (a r : V) (σ π τ : List V)
    (har : a < r) (haσ : ∀ b ∈ σ, a < b) :
    Z (a :: r :: σ ++ π) (a :: σ ++ [r] ++ τ) =
      Z (r :: σ ++ [a] ++ π) (σ ++ [r, a] ++ τ) +
        q * ∑ i ∈ Finset.range (σ.length + 1),
          Z (r :: (σ.take i ++ a :: σ.drop i) ++ π)
            ((σ.take i ++ a :: σ.drop i) ++ [r] ++ τ) := by
  have hx : ∀ b ∈ r :: σ, a < b := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact har
    · exact haσ b hb
  have hy : ∀ b ∈ σ ++ [r], a < b := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact haσ b hb
    · have hb' : b = r := List.mem_singleton.mp hb
      simpa only [hb'] using har
  have h := minimumSlide hZ a π τ [] [] (r :: σ) (σ ++ [r]) rfl (by simp) hx hy
  rw [minimumSlideSum_eq_sum Z a π τ [] [] (r :: σ) (σ ++ [r]) (by simp)] at h
  simp only [List.nil_append, List.length_cons, List.cons_append, List.append_assoc] at h ⊢
  convert h using 2
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ σ.length := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  simp [List.take_succ_cons, List.drop_succ_cons,
    List.take_append_of_le_length hi', List.drop_append_of_le_length hi',
    List.append_assoc]

end Semiring

section Ring

variable [CommRing R]

/-- A mountain lists the unmarked vertices increasingly, then the root, then marks decreasingly. -/
def mountainList (U T : Finset V) (r : V) : List V :=
  ((U.erase r) \ T).sort ++ [r] ++ T.sort (· ≥ ·)

/-- The signed prefix functional before the positive root-deletion theorem. -/
noncomputable def signedRootDeletion (Z : List V → List V → R)
    (U : Finset V) (r : V) (π τ : List V) : R :=
  ∑ T ∈ (U.erase r).powerset,
    (-1 : R) ^ T.card * Z (mountainList U T r ++ π) (mountainList U T r ++ τ)

private theorem sort_insert_min_decreasing (T : Finset V) (a : V)
    (ha : ∀ b ∈ T, a < b) :
    (insert a T).sort (· ≥ ·) = T.sort (· ≥ ·) ++ [a] := by
  have hnot : a ∉ T := fun h => (lt_irrefl a) (ha a h)
  have hd : Disjoint T {a} := by simp [hnot]
  have ht : IsOrder T (T.sort (· ≥ ·)) := (decreasingOrder T).property
  have hs : IsOrder {a} [a] := by simp [IsOrder]
  have ho := ht.append hs hd
  have hp : (T.sort (· ≥ ·) ++ [a]).Pairwise (· ≥ ·) := by
    rw [List.pairwise_append]
    refine ⟨T.pairwise_sort _, by simp, ?_⟩
    intro b hb c hc
    have hc' : c = a := List.mem_singleton.mp hc
    subst c
    exact le_of_lt (ha b ((ht.mem_iff b).mp hb))
  have h := (List.toFinset_sort ho.1).mpr hp
  simpa only [ho.2, Finset.union_singleton] using h

private theorem mountainList_insert_min_unmarked (U T : Finset V) (r a : V)
    (har : a < r) (ha : ∀ b ∈ U, a < b) (hT : T ⊆ U.erase r) :
    mountainList (insert a U) T r = a :: mountainList U T r := by
  have haT : a ∉ T := fun h => (lt_irrefl a) (ha a (Finset.mem_of_mem_erase (hT h)))
  have heq : ((insert a U).erase r) \ T = insert a ((U.erase r) \ T) := by
    ext b
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hbr, rfl | hb⟩, hbT⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hbr, hb⟩, hbT⟩
    · rintro (rfl | ⟨⟨hbr, hb⟩, hbT⟩)
      · exact ⟨⟨ne_of_lt har, Or.inl rfl⟩, haT⟩
      · exact ⟨⟨hbr, Or.inr hb⟩, hbT⟩
  have hsmall : ∀ b ∈ (U.erase r) \ T, a ≤ b := by
    intro b hb
    exact le_of_lt (ha b (Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hb).1))
  have hnot' : a ∉ (U.erase r) \ T := by
    intro h
    exact (lt_irrefl a) (ha a (Finset.mem_of_mem_erase (Finset.mem_sdiff.mp h).1))
  simp only [mountainList, heq, Finset.sort_insert _ hsmall hnot', List.cons_append]

private theorem mountainList_insert_min_marked (U T : Finset V) (r a : V)
    (_har : a < r) (ha : ∀ b ∈ U, a < b) (hT : T ⊆ U.erase r) :
    mountainList (insert a U) (insert a T) r = mountainList U T r ++ [a] := by
  have haU : a ∉ U := fun h => (lt_irrefl a) (ha a h)
  have heq : ((insert a U).erase r) \ insert a T = (U.erase r) \ T := by
    ext b
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
    aesop
  have hsmall : ∀ b ∈ T, a < b := fun b hb =>
    ha b (Finset.mem_of_mem_erase (hT hb))
  simp only [mountainList, heq, sort_insert_min_decreasing T a hsmall, List.append_assoc]

end Ring

end VerticalStripLLT.CyclicHessenberg
