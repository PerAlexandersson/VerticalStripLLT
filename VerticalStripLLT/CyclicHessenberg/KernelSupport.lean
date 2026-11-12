import VerticalStripLLT.CyclicHessenberg.RootDeletion

/-! Support of a zero-extended kernel and its actual positive residuals. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V R : Type*} [LinearOrder V] [CommSemiring R]

/-- Both boundary words must list the given support exactly once. -/
def SupportedKernel (S : Finset V) (Z : List V → List V → R) : Prop :=
  ∀ l t, (¬ IsOrder S l ∨ ¬ IsOrder S t) → Z l t = 0

theorem kernelEntry_supported (S : Finset V) (Z : Kernel R S) :
    SupportedKernel S (kernelEntry Z) := by
  classical
  intro l t h
  change f (Z l t) = 0
  rcases h with hl | ht
  · simp [kernelEntry, hl]
  · by_cases hl : IsOrder S l <;> simp [kernelEntry, hl, ht]

theorem SupportedKernel.map {S : Finset V} {Z : List V → List V → R}
    (hZ : SupportedKernel S Z) {T : Type*} [CommSemiring T] (f : R →+* T) :
    SupportedKernel S (fun l t => f (Z l t)) := by
  intro l t h
  rw [hZ l t h, map_zero]

theorem SupportedKernel.diagonal_repeated {S : Finset V}
    {Z : List V → List V → R} (hZ : SupportedKernel S Z) (w : List V)
    (hw : ¬ w.Nodup) : Z w w = 0 :=
  hZ w w (Or.inl (fun h => hw h.1))

theorem SupportedKernel.diagonal_degree {S : Finset V}
    {Z : List V → List V → R} (hZ : SupportedKernel S Z) (w : List V)
    (hw : S.card < w.length) : Z w w = 0 := by
  apply hZ w w
  left
  intro h
  have hh := h.length
  lia

theorem rootPrefix_isOrder (U : Finset V) (r : V) (hr : r ∈ U)
    (σ : Order (U.erase r)) : IsOrder U (r :: σ.val) := by
  classical
  constructor
  · apply List.nodup_cons.mpr
    refine ⟨?_, σ.property.1⟩
    intro h
    exact Finset.notMem_erase r U ((mem_order σ r).mp h)
  · simp only [List.toFinset_cons, σ.property.2, Finset.insert_erase hr]

theorem rotatedRootPrefix_isOrder (U : Finset V) (r : V) (hr : r ∈ U)
    (σ : Order (U.erase r)) : IsOrder U (σ.val ++ [r]) := by
  have hh : IsOrder U ([r] ++ σ.val) := rootPrefix_isOrder U r hr σ
  exact hh.perm List.perm_append_comm

/-- A signed mountain contains exactly its chosen vertices and the additional root. -/
theorem mountain_isOrder (U T : Finset V) (r : V) (hr : r ∉ U) (hT : T ⊆ U) :
    IsOrder (insert r U) ((U \ T).sort ++ [r] ++ T.sort (· ≥ ·)) := by
  classical
  have hrT : r ∉ T := fun h => hr (hT h)
  have h₁ : Disjoint (U \ T) {r} := by
    simp only [Finset.disjoint_singleton_right, Finset.mem_sdiff, not_and]
    exact fun h => (hr h).elim
  have h₂ : Disjoint ((U \ T) ∪ {r}) T := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.sdiff_disjoint, by simpa using hrT⟩
  have hp := (((increasingOrder (U \ T)).property.append
    (show IsOrder ({r} : Finset V) [r] by simp [IsOrder]) h₁).append
      (decreasingOrder T).property h₂)
  have hs : ((U \ T) ∪ {r}) ∪ T = insert r U := by
    calc
      _ = {r} ∪ ((U \ T) ∪ T) := by ac_rfl
      _ = insert r U := by rw [Finset.sdiff_union_of_subset hT]; simp
  rw [hs] at hp
  exact hp

/-- Positive deletion really removes `U`; it retains neither repetitions nor missing letters. -/
theorem SupportedKernel.rootDeletion {S : Finset V} {Z : List V → List V → R}
    (hZ : SupportedKernel S Z) (q : R) (U : Finset V) (hUS : U ⊆ S)
    (r : V) (hr : r ∈ U) : SupportedKernel (S \ U) (rootDeletion q Z U r) := by
  classical
  intro π τ hbad
  have hzero : (∑ σ : Order (U.erase r),
      Z ((r :: σ.val) ++ π) ((σ.val ++ [r]) ++ τ)) = 0 := by
    apply Finset.sum_eq_zero
    intro σ hσ
    apply hZ
    have hleft := isOrder_append_left_iff (B := S \ U) (l := π)
      (rootPrefix_isOrder U r hr σ) Finset.sdiff_disjoint.symm
    have hright := isOrder_append_left_iff (B := S \ U) (l := τ)
      (rotatedRootPrefix_isOrder U r hr σ) Finset.sdiff_disjoint.symm
    rw [Finset.union_sdiff_of_subset hUS] at hleft hright
    rcases hbad with hπ | hτ
    · exact Or.inl (fun h => hπ (hleft.mp h))
    · exact Or.inr (fun h => hτ (hright.mp h))
  change rootDeletion q Z U r π τ = 0
  simp only [rootDeletion, hzero, mul_zero]

end VerticalStripLLT.CyclicHessenberg
