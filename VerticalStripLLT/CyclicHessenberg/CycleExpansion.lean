import VerticalStripLLT.CyclicHessenberg.CycleDisplayFinite
import VerticalStripLLT.CyclicHessenberg.CycleDisplayShape
import VerticalStripLLT.CyclicHessenberg.Expansion

/-! Unroll positive root deletion into literal, fixed-point-inclusive cycle displays. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V : Type*} [LinearOrder V]

noncomputable def cycleWeight (S : Finset V) (Z : List V → List V → Polynomial ℕ)
    (D : CycleDisplay S) : NEExpansion :=
  MvPolynomial.C (Polynomial.X ^ (S.card - D.count) * Z D.source.val D.target.val) *
    D.elementaryMonomial

/-- This finite expression is defined directly from canonical cycles, without recursion. -/
noncomputable def naturalCycleSum (S : Finset V)
    (Z : List V → List V → Polynomial ℕ) : NEExpansion :=
  ∑ D : CycleDisplay S, cycleWeight S Z D

theorem sum_cycleDisplays {R : Type*} [AddCommMonoid R] (S : Finset V) (r : V)
    (hr : r ∈ S) (hmax : ∀ a ∈ S, a ≤ r) (F : CycleDisplay S → R) :
    ∑ D, F D = ∑ U : CycleDisplay.RootSet S r, ∑ σ : Order (U.val.erase r),
      ∑ D : CycleDisplay (S \ U.val),
        F (CycleDisplay.cons S U.val r U.property.1 U.property.2 hmax σ D) := by
  classical
  rw [← (CycleDisplay.deletionEquiv S r hr hmax).sum_comp F, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Fintype.sum_prod_type]
  rfl

theorem cycleWeight_cons (S U : Finset V) (r : V) (hUS : U ⊆ S) (hr : r ∈ U)
    (hmax : ∀ a ∈ S, a ≤ r) (σ : Order (U.erase r))
    (D : CycleDisplay (S \ U)) (Z : List V → List V → Polynomial ℕ) :
    cycleWeight S Z (CycleDisplay.cons S U r hUS hr hmax σ D) =
      natElementary ⟨U.card, Finset.card_pos.mpr ⟨r, hr⟩⟩ *
        MvPolynomial.C (Polynomial.X ^ ((S \ U).card - D.count) *
          Polynomial.X ^ (U.card - 1) *
          Z ((r :: σ.val) ++ D.source.val) ((σ.val ++ [r]) ++ D.target.val)) *
        D.elementaryMonomial := by
  have hc := Finset.card_sdiff_add_card_eq_card hUS
  have hd := D.count_le_card
  have hu := Finset.card_pos.mpr ⟨r, hr⟩
  have hexp : S.card - (1 + D.count) = ((S \ U).card - D.count) + (U.card - 1) := by
    lia
  have hsize : CycleDisplay.blockSize (r, σ.val) =
      ⟨U.card, Finset.card_pos.mpr ⟨r, hr⟩⟩ := by
    apply Subtype.ext
    change σ.val.length + 1 = U.card
    rw [length_order, Finset.card_erase_of_mem hr]
    lia
  simp only [cycleWeight, CycleDisplay.cons_count, CycleDisplay.cons_source_val,
    CycleDisplay.cons_target_val, hexp, pow_add, map_mul]
  change _ * (natElementary (CycleDisplay.blockSize (r, σ.val)) * D.elementaryMonomial) = _
  rw [hsize]
  ring

theorem naturalCycleSum_eq_rootSum (S : Finset V) (r : V) (hr : r ∈ S)
    (hmax : ∀ a ∈ S, a ≤ r) (Z : List V → List V → Polynomial ℕ) :
    naturalCycleSum S Z =
      ∑ U : CycleDisplay.RootSet S r,
        natElementary ⟨U.val.card, Finset.card_pos.mpr ⟨r, U.property.2⟩⟩ *
          naturalCycleSum (S \ U.val) (rootDeletion Polynomial.X Z U.val r) := by
  classical
  rw [naturalCycleSum, sum_cycleDisplays S r hr hmax]
  apply Finset.sum_congr rfl
  intro U hU
  simp_rw [cycleWeight_cons]
  rw [Finset.sum_comm]
  simp only [naturalCycleSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  simp only [cycleWeight, rootDeletion, Finset.mul_sum, map_sum, map_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  ring

private theorem sum_rootSet {R : Type*} [AddCommMonoid R]
    (S : Finset V) (r : V) (F : ∀ U : Finset V, r ∈ U → R) :
    (∑ U : S.powerset, if hr : r ∈ U.val then F U.val hr else 0) =
      ∑ U : CycleDisplay.RootSet S r, F U.val U.property.2 := by
  classical
  let g : Finset V → R := fun U => if hr : r ∈ U then F U hr else 0
  change (∑ U : S.powerset, g U.val) = _
  rw [Finset.sum_coe_sort]
  calc
    ∑ U ∈ S.powerset, g U = ∑ U ∈ S.powerset.filter (fun U => r ∈ U), g U := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro U hU
      by_cases hr : r ∈ U <;> simp only [g, hr, dite_true, dite_false, ite_true, ite_false]
    _ = ∑ U : CycleDisplay.RootSet S r, g U.val :=
      Finset.sum_subtype _ (by simp) g
    _ = ∑ U : CycleDisplay.RootSet S r, F U.val U.property.2 := by
      apply Finset.sum_congr rfl
      intro U hU
      exact dite_eq_left U.property.2

/-- The recursive expansion is exactly the explicit canonical-cycle sum. -/
theorem naturalKernelExpansion_eq_cycleSum (S : Finset V)
    (Z : List V → List V → Polynomial ℕ) :
    naturalKernelExpansion S Z = naturalCycleSum S Z := by
  classical
  induction S using Finset.strongInductionOn generalizing Z with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · let r := S.max' hS
      have hr : r ∈ S := S.max'_mem hS
      have hmax : ∀ a ∈ S, a ≤ r := fun a ha => Finset.le_max' S a ha
      have hsum := sum_rootSet S r (fun U hroot =>
        natElementary ⟨U.card, Finset.card_pos.mpr ⟨r, hroot⟩⟩ *
          naturalKernelExpansion (S \ U) (rootDeletion Polynomial.X Z U r))
      calc
        naturalKernelExpansion S Z = _ :=
          (naturalKernelExpansion_eq_rootSum S hS Z).trans hsum
        _ = naturalCycleSum S Z := ?_
      rw [naturalCycleSum_eq_rootSum S r hr hmax]
      apply Finset.sum_congr rfl
      intro U hU
      rw [ih (S \ U.val) (Finset.sdiff_ssubset U.property.1 ⟨r, U.property.2⟩)]
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      simp [naturalCycleSum, cycleWeight, CycleDisplay.count, CycleDisplay.source,
        CycleDisplay.target, CycleDisplay.elementaryMonomial, cycleSourceWord, cycleTargetWord]

end VerticalStripLLT.CyclicHessenberg
