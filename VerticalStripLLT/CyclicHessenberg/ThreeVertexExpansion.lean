import VerticalStripLLT.CyclicHessenberg.SmallOrders
import VerticalStripLLT.CyclicHessenberg.TwoVertexExpansion

set_option autoImplicit false

/-! The natural recursive expansion on three named vertices. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V : Type*} [LinearOrder V]

/-- The positive recurrence on three vertices, expanded by its four root subsets. -/
theorem naturalKernelExpansion_triple (a b r : V) (hab : a < b) (hbr : b < r)
    (Z : List V → List V → Polynomial ℕ) :
    naturalKernelExpansion {r, b, a} Z =
      MvPolynomial.C (Z [r, b, a] [r, b, a]) * natElementary 1 ^ 3 +
        MvPolynomial.C (Polynomial.X *
          (Z [r, b, a] [r, a, b] + Z [r, a, b] [a, r, b] +
            Z [r, b, a] [b, r, a])) * natElementary 2 * natElementary 1 +
        MvPolynomial.C (Polynomial.X ^ 2 *
          (Z [r, b, a] [b, a, r] + Z [r, a, b] [a, b, r])) * natElementary 3 := by
  classical
  let S : Finset V := {b, a}
  have habne : a ≠ b := ne_of_lt hab
  have hbrne : b ≠ r := ne_of_lt hbr
  have harne : a ≠ r := ne_of_lt (lt_trans hab hbr)
  have hmax : ∀ x ∈ S, x < r := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hbr
    · exact lt_trans hab hbr
  have hpa : ({a} : Finset V).powerset = {∅, {a}} := by
    ext U
    simp only [Finset.mem_powerset, Finset.subset_singleton_iff,
      Finset.mem_insert, Finset.mem_singleton]
  have hps : S.powerset = {∅, {a}, {b}, {b, a}} := by
    rw [show S = insert b {a} from rfl, Finset.powerset_insert, hpa]
    simp only [Finset.image_singleton, Finset.image_insert, Finset.insert_empty]
    ext U
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hdiff0 : (insert r S : Finset V) \ {r} = S := by
    ext x
    simp only [S, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hdiffA : (insert r S : Finset V) \ {r, a} = {b} := by
    ext x
    simp only [S, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hdiffB : (insert r S : Finset V) \ {r, b} = {a} := by
    ext x
    simp only [S, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hdiffAB : (insert r S : Finset V) \ (insert r {b, a}) = ∅ := by
    exact Finset.sdiff_self _
  let Z0 := rootDeletion (Polynomial.X : Polynomial ℕ) Z {r} r
  let f : Finset V → NEExpansion := fun U =>
    natElementary ⟨U.card + 1, Nat.zero_lt_succ _⟩ *
      naturalKernelExpansion ((insert r S) \ (insert r U))
        (rootDeletion Polynomial.X Z (insert r U) r)
  have hsum :
      (∑ U ∈ S.powerset, f U) =
        f ∅ + f {a} + f {b} + f {b, a} := by
    rw [hps]
    have ha : ({a} : Finset V) ≠ {b} := by
      intro hh
      exact habne (Finset.singleton_injective hh)
    have habset : ({a} : Finset V) ≠ {b, a} := by
      intro hh
      have hb : b ∈ ({a} : Finset V) := hh.symm ▸ Finset.mem_insert_self b {a}
      exact habne.symm (Finset.mem_singleton.mp hb)
    have hbaset : ({b} : Finset V) ≠ {b, a} := by
      intro hh
      have ha' : a ∈ ({b} : Finset V) := hh.symm ▸ Finset.mem_insert_of_mem (by simp)
      exact habne (Finset.mem_singleton.mp ha')
    rw [Finset.sum_insert (show (∅ : Finset V) ∉ {{a}, {b}, {b, a}} by simp),
      Finset.sum_insert (show ({a} : Finset V) ∉ {{b}, {b, a}} by simp [ha, habset]),
      Finset.sum_insert (show ({b} : Finset V) ∉ {{b, a}} by simp [hbaset]),
      Finset.sum_singleton]
    simp only [add_assoc]
  have hrecFour : naturalKernelExpansion (insert r S) Z =
      f ∅ + f {a} + f {b} + f {b, a} := by
    calc
      naturalKernelExpansion (insert r S) Z = ∑ U ∈ S.powerset, f U := by
        rw [naturalKernelExpansion_insert_max S r hmax Z]
      _ = _ := hsum
  have hrootA :
      rootDeletion (Polynomial.X : Polynomial ℕ) Z {r, a} r [b] [b] =
        Polynomial.X * Z [r, a, b] [a, r, b] := by
    unfold rootDeletion
    have herase : ({r, a} : Finset V).erase r = {a} := by
      simp [harne, harne.symm]
    rw [herase]
    simp [harne, harne.symm]
  have hrootB :
      rootDeletion (Polynomial.X : Polynomial ℕ) Z {r, b} r [a] [a] =
        Polynomial.X * Z [r, b, a] [b, r, a] := by
    unfold rootDeletion
    have herase : ({r, b} : Finset V).erase r = {b} := by
      simp [hbrne, hbrne.symm]
    rw [herase]
    simp [hbrne, hbrne.symm]
  have hrootAB :
      rootDeletion (Polynomial.X : Polynomial ℕ) Z (insert r {b, a}) r [] [] =
        Polynomial.X ^ 2 *
          (Z [r, b, a] [b, a, r] + Z [r, a, b] [a, b, r]) := by
    unfold rootDeletion
    have herase : (insert r ({b, a} : Finset V)).erase r = {b, a} := by
      simp [hbrne, hbrne.symm, harne, harne.symm]
    have hcard : (insert r ({b, a} : Finset V)).card = 3 := by
      simp [habne, habne.symm, hbrne, hbrne.symm, harne, harne.symm]
    rw [herase, hcard]
    rw [sum_order_pair b a habne.symm]
    simp [pairForwardOrder, pairReverseOrder, habne, Finset.pair_comm]
  have hrecExplicit : naturalKernelExpansion {r, b, a} Z =
      natElementary 1 * naturalKernelExpansion {b, a} Z0 +
        natElementary 2 * naturalKernelExpansion {b}
          (rootDeletion Polynomial.X Z {r, a} r) +
        natElementary 2 * naturalKernelExpansion {a}
          (rootDeletion Polynomial.X Z {r, b} r) +
        natElementary 3 * naturalKernelExpansion ∅
          (rootDeletion Polynomial.X Z (insert r {b, a}) r) := by
    have hh := hrecFour
    simp only [Z0, f, Finset.card_empty, Finset.card_singleton, Finset.insert_empty,
      Finset.card_insert_of_notMem (show b ∉ ({a} : Finset V) by simp [habne.symm]),
      hdiff0, hdiffA, hdiffB, hdiffAB, S] at hh
    exact hh
  rw [hrecExplicit]
  rw [naturalKernelExpansion_pair a b hab Z0,
    naturalKernelExpansion_singleton b (rootDeletion Polynomial.X Z {r, a} r),
    naturalKernelExpansion_singleton a (rootDeletion Polynomial.X Z {r, b} r),
    naturalKernelExpansion_empty]
  simp only [Z0, rootDeletion_singleton]
  rw [hrootA, hrootB, hrootAB]
  simp only [map_add, map_mul]
  ring

end VerticalStripLLT.CyclicHessenberg
