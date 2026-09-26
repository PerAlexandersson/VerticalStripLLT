import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith

open scoped BigOperators Classical

namespace VerticalStripLLT.Circular.ChainSingletonSubsets

variable {E R : Type*} [CommRing R]

/-- Remove edges that are either forced (factor `1 + q`) or killing (factor `1`). -/
theorem powerset_reduce (N T : Finset E) (hT : T ⊆ N) (f : Finset E → R) (q : R)
    (P : E → Prop)
    (hforced : ∀ e ∈ T, P e → ∀ A ⊆ N, f (insert e A) = f A)
    (hkill : ∀ e ∈ T, ¬ P e → ∀ A ⊆ N, f (insert e A) = 0) :
    ∑ A ∈ N.powerset, q ^ A.card * f A =
      (1 + q) ^ (T.filter P).card * ∑ A ∈ (N \ T).powerset, q ^ A.card * f A := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert e T heT ih =>
    have heN : e ∈ N := hT (Finset.mem_insert_self _ _)
    have hTN : T ⊆ N := (Finset.subset_insert _ _).trans hT
    rw [ih hTN (fun e' he' => hforced e' (Finset.mem_insert_of_mem he'))
      (fun e' he' => hkill e' (Finset.mem_insert_of_mem he'))]
    have hsplit : N \ T = insert e (N \ insert e T) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨hx, hxT⟩
        by_cases hxe : x = e
        · exact Or.inl hxe
        · exact Or.inr ⟨hx, fun h => h.elim hxe hxT⟩
      · rintro (rfl | ⟨hx, hxT⟩)
        · exact ⟨heN, heT⟩
        · exact ⟨hx, fun h => hxT (Or.inr h)⟩
    have hen : e ∉ N \ insert e T := by simp
    rw [hsplit, Finset.sum_powerset_insert hen]
    have hsubN : ∀ A ∈ (N \ insert e T).powerset, A ⊆ N := fun A hA =>
      (Finset.mem_powerset.mp hA).trans Finset.sdiff_subset
    have hcard : ∀ A ∈ (N \ insert e T).powerset, (insert e A).card = A.card + 1 := by
      intro A hA
      apply Finset.card_insert_of_notMem
      intro h
      have := Finset.mem_powerset.mp hA h
      simp at this
    by_cases hP : P e
    · have hfil : (insert e T).filter P = insert e (T.filter P) := by
        rw [Finset.filter_insert, ite_eq_left hP]
      rw [hfil, Finset.card_insert_of_notMem (by simp [heT])]
      have h2 : ∀ A ∈ (N \ insert e T).powerset,
          q ^ (insert e A).card * f (insert e A) = q * (q ^ A.card * f A) := by
        intro A hA
        rw [hcard A hA, hforced e (Finset.mem_insert_self _ _) hP A (hsubN A hA)]
        ring
      rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
      ring
    · have hfil : (insert e T).filter P = T.filter P := by
        rw [Finset.filter_insert, ite_eq_right hP]
      rw [hfil]
      have h2 : ∀ A ∈ (N \ insert e T).powerset,
          q ^ (insert e A).card * f (insert e A) = 0 := by
        intro A hA
        rw [hkill e (Finset.mem_insert_self _ _) hP A (hsubN A hA), mul_zero]
      rw [Finset.sum_congr rfl h2, Finset.sum_const_zero, add_zero]

/-- Subsets of a disjoint union are pairs of subsets. -/
theorem sum_powerset_disjoint_union [DecidableEq E] (X Y : Finset E) (hXY : Disjoint X Y)
    (F : Finset E → R) :
    ∑ A ∈ (X ∪ Y).powerset, F A =
      ∑ P ∈ X.powerset, ∑ Q ∈ Y.powerset, F (P ∪ Q) := by
  rw [← Finset.sum_product']
  symm
  apply Finset.sum_nbij' (fun p => p.1 ∪ p.2) (fun A => (A ∩ X, A ∩ Y))
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_powerset] at hp ⊢
    exact Finset.union_subset_union hp.1 hp.2
  · intro A hA
    simp only [Finset.mem_product, Finset.mem_powerset] at hA ⊢
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_powerset] at hp
    have h1 : (p.1 ∪ p.2) ∩ X = p.1 := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp.1]
      have : p.2 ∩ X = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        rw [Finset.mem_inter] at hx
        exact Finset.disjoint_left.mp hXY hx.2 (hp.2 hx.1)
      rw [this, Finset.union_empty]
    have h2 : (p.1 ∪ p.2) ∩ Y = p.2 := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hp.2]
      have : p.1 ∩ Y = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        rw [Finset.mem_inter] at hx
        exact Finset.disjoint_left.mp hXY (hp.1 hx.1) hx.2
      rw [this, Finset.empty_union]
    simp [h1, h2]
  · intro A hA
    simp only [Finset.mem_powerset] at hA
    simp only
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hA]
  · intro p hp
    rfl

/-- Subsets of a finset correspond to subsets of an injective image. -/
theorem sum_powerset_image {ι : Type*} [DecidableEq ι] (X : Finset E) (p : E → ι)
    (hp : Set.InjOn p X) (F : Finset ι → R) :
    ∑ A ∈ X.powerset, F (A.image p) = ∑ U ∈ (X.image p).powerset, F U := by
  apply Finset.sum_nbij' (fun A => A.image p) (fun U => X.filter (fun e => p e ∈ U))
  · intro A hA
    simp only [Finset.mem_powerset] at hA ⊢
    exact Finset.image_subset_image hA
  · intro U _
    simp only [Finset.mem_powerset]
    exact Finset.filter_subset _ _
  · intro A hA
    simp only [Finset.mem_powerset] at hA
    ext e
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨heX, e', he'A, he'⟩
      rwa [← hp (hA he'A) heX he']
    · intro heA
      exact ⟨hA heA, e, heA, rfl⟩
  · intro U hU
    simp only [Finset.mem_powerset] at hU
    ext i
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨e, ⟨_, he⟩, rfl⟩
      exact he
    · intro hi
      obtain ⟨e, heX, rfl⟩ := Finset.mem_image.mp (hU hi)
      exact ⟨e, ⟨heX, hi⟩, rfl⟩
  · intro A _
    rfl

theorem sum_powerset_union_image {ι : Type*} [DecidableEq E] [DecidableEq ι]
    (X Y : Finset E) (hXY : Disjoint X Y) (px py : E → ι)
    (hx : Set.InjOn px X) (hy : Set.InjOn py Y) (g : Finset ι → Finset ι → R) (q : R) :
    ∑ A ∈ (X ∪ Y).powerset, q ^ A.card * g ((A ∩ X).image px) ((A ∩ Y).image py) =
      ∑ U ∈ (X.image px).powerset, ∑ V ∈ (Y.image py).powerset,
        q ^ (U.card + V.card) * g U V := by
  rw [sum_powerset_disjoint_union X Y hXY]
  have hterm : ∀ P ∈ X.powerset, ∀ Q ∈ Y.powerset,
      q ^ (P ∪ Q).card * g (((P ∪ Q) ∩ X).image px) (((P ∪ Q) ∩ Y).image py) =
        q ^ ((P.image px).card + (Q.image py).card) * g (P.image px) (Q.image py) := by
    intro P hP Q hQ
    have hP' := Finset.mem_powerset.mp hP
    have hQ' := Finset.mem_powerset.mp hQ
    have hdPQ : Disjoint P Q := Finset.disjoint_of_subset_left hP'
      (Finset.disjoint_of_subset_right hQ' hXY)
    have h1 : (P ∪ Q) ∩ X = P := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hP']
      have : Q ∩ X = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        rw [Finset.mem_inter] at hx
        exact Finset.disjoint_left.mp hXY hx.2 (hQ' hx.1)
      rw [this, Finset.union_empty]
    have h2 : (P ∪ Q) ∩ Y = Q := by
      rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hQ']
      have : P ∩ Y = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        rw [Finset.mem_inter] at hx
        exact Finset.disjoint_left.mp hXY (hP' hx.1) hx.2
      rw [this, Finset.empty_union]
    rw [h1, h2, Finset.card_union_of_disjoint hdPQ,
      Finset.card_image_of_injOn (hx.mono (by exact_mod_cast hP')),
      Finset.card_image_of_injOn (hy.mono (by exact_mod_cast hQ'))]
  rw [Finset.sum_congr rfl (fun P hP => Finset.sum_congr rfl (hterm P hP))]
  rw [sum_powerset_image X px hx (fun U => ∑ Q ∈ Y.powerset,
    q ^ (U.card + (Q.image py).card) * g U (Q.image py))]
  apply Finset.sum_congr rfl
  intro U _
  exact sum_powerset_image Y py hy (fun V => q ^ (U.card + V.card) * g U V)

end VerticalStripLLT.Circular.ChainSingletonSubsets

