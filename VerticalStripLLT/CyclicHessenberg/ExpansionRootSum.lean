import VerticalStripLLT.CyclicHessenberg.Expansion
import VerticalStripLLT.CyclicHessenberg.RootSubsetSums

/-! The natural recurrence indexed by subsets below an additional largest root. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V : Type*} [LinearOrder V]

theorem naturalKernelExpansion_insert_max (S : Finset V) (r : V)
    (hr : ∀ a ∈ S, a < r) (Z : List V → List V → Polynomial ℕ) :
    naturalKernelExpansion (insert r S) Z =
      ∑ U ∈ S.powerset, natElementary ⟨U.card + 1, Nat.zero_lt_succ _⟩ *
        naturalKernelExpansion ((insert r S) \ (insert r U))
          (rootDeletion Polynomial.X Z (insert r U) r) := by
  classical
  have hrS : r ∉ S := fun h => (lt_irrefl r) (hr r h)
  have hne : (insert r S).Nonempty := ⟨r, Finset.mem_insert_self _ _⟩
  have hmax : (insert r S).max' hne = r := by
    apply (Finset.max'_eq_iff _ _ _).mpr
    refine ⟨Finset.mem_insert_self _ _, ?_⟩
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact le_rfl
    · exact (hr a ha).le
  rw [naturalKernelExpansion_eq_rootSum _ hne, hmax]
  rw [sum_powerset_insert_indicator S r hrS]
  apply Finset.sum_congr rfl
  intro U hU
  have hrU : r ∉ U := fun h => hrS (Finset.mem_powerset.mp hU h)
  simp only [Finset.card_insert_of_notMem hrU]

end VerticalStripLLT.CyclicHessenberg
