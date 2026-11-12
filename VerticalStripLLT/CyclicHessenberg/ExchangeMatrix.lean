import VerticalStripLLT.CyclicHessenberg.Kernel
import VerticalStripLLT.CyclicHessenberg.MatrixExchange

/-! Scalar list exchange is equivalent to adjacent-position matrix commutation. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V R : Type*} [LinearOrder V] [CommSemiring R]

/-- The exchange acts on adjacent positions of orders, keeping vertex names fixed. -/
noncomputable def exchangeMatrix (q : R) (S : Finset V) (i : ℕ) : Kernel R S := by
  classical
  exact involutionExchange (swapAdjacent i) (fun l => IncreasingAt i l.val) q

/-- Translate all scalar list exchanges to the corresponding finite involutions. -/
theorem exchangeCompatible_iff_involutions (q : R) {S : Finset V} (Z : Kernel R S) :
    ExchangeCompatible q Z ↔ ∀ i, i + 1 < S.card →
      InvolutionExchangeCompatible (swapAdjacent i)
        (fun l : Order S => IncreasingAt i l.val) q Z := by
  classical
  constructor
  · intro hZ i hi x y hx hy
    obtain ⟨ρ, σ, a, b, hρ, hl⟩ := adjacent_context i x.val (by simpa using hi)
    obtain ⟨ρ', σ', c, d, hρ', ht⟩ := adjacent_context i y.val (by simpa using hi)
    have hab : a < b := by
      rw [hl, ← hρ, increasingAt_context] at hx
      exact hx
    have hcd : c < d := by
      rw [ht, ← hρ', increasingAt_context] at hy
      exact hy
    have hxl : (swapAdjacent i x).val = ρ ++ [b, a] ++ σ := by
      change swapAdjacentList i x.val = _
      rw [hl, ← hρ, swapAdjacentList_context]
    have hyt : (swapAdjacent i y).val = ρ' ++ [d, c] ++ σ' := by
      change swapAdjacentList i y.val = _
      rw [ht, ← hρ', swapAdjacentList_context]
    have h := hZ ρ σ ρ' σ' a b c d (hρ.trans hρ'.symm) hab hcd
    rw [← hl, ← ht, ← hxl, ← hyt] at h
    simpa only [kernelEntry_order] using h
  · intro h ρ σ ρ' σ' a b c d hlen hab hcd
    by_cases hl : IsOrder S (ρ ++ [a, b] ++ σ)
    · have hl' := isOrder_swapAdjacent ρ σ a b hl
      by_cases ht : IsOrder S (ρ' ++ [c, d] ++ σ')
      · have ht' := isOrder_swapAdjacent ρ' σ' c d ht
        let x : Order S := ⟨ρ ++ [a, b] ++ σ, hl⟩
        let y : Order S := ⟨ρ' ++ [c, d] ++ σ', ht⟩
        have hi : ρ.length + 1 < S.card := by
          have hh := hl.length
          simp only [List.length_append, List.length_cons, List.length_nil] at hh
          lia
        have hx : IncreasingAt ρ.length x.val := (increasingAt_context ρ σ a b).mpr hab
        have hy : IncreasingAt ρ.length y.val := by
          rw [hlen]
          exact (increasingAt_context ρ' σ' c d).mpr hcd
        have hh := h ρ.length hi x y hx hy
        have hsx : swapAdjacent ρ.length x = ⟨ρ ++ [b, a] ++ σ, hl'⟩ := by
          apply Subtype.ext
          exact swapAdjacentList_context ρ σ a b
        have hsy : swapAdjacent ρ.length y = ⟨ρ' ++ [d, c] ++ σ', ht'⟩ := by
          apply Subtype.ext
          change swapAdjacentList ρ.length (ρ' ++ [c, d] ++ σ') = _
          rw [hlen, swapAdjacentList_context]
        rw [hsx, hsy] at hh
        simpa only [kernelEntry, dite_eq_left hl, dite_eq_left hl', dite_eq_left ht, dite_eq_left ht'] using hh
      · have ht' : ¬ IsOrder S (ρ' ++ [d, c] ++ σ') :=
          fun h' => ht (isOrder_swapAdjacent ρ' σ' d c h')
        simp only [kernelEntry, dite_eq_left hl, dite_eq_left hl', dite_eq_right ht,
          dite_eq_right ht', mul_zero, add_zero, and_self]
    · have hl' : ¬ IsOrder S (ρ ++ [b, a] ++ σ) :=
        fun h' => hl (isOrder_swapAdjacent ρ σ b a h')
      simp only [kernelEntry, dite_eq_right hl, dite_eq_right hl', mul_zero,
        add_zero, and_self]

/-- Commutation is a consequence and characterization of the scalar laws. -/
theorem exchangeCompatible_iff_commute (q : R) {S : Finset V} (Z : Kernel R S) :
    ExchangeCompatible q Z ↔ ∀ i, i + 1 < S.card →
      Z * exchangeMatrix q S i = exchangeMatrix q S i * Z := by
  classical
  rw [exchangeCompatible_iff_involutions]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  exact involutionExchangeCompatible_iff_commute _ _ q Z
    (swapAdjacent_involutive i) (increasingAt_swapAdjacent i hi)

/-- The scalar laws survive multiplication of transfer kernels. -/
theorem ExchangeCompatible.mul {q : R} {S : Finset V} {Z W : Kernel R S}
    (hZ : ExchangeCompatible q Z) (hW : ExchangeCompatible q W) :
    ExchangeCompatible q (Z * W) := by
  classical
  rw [exchangeCompatible_iff_commute] at hZ hW ⊢
  intro i hi
  calc
    (Z * W) * exchangeMatrix q S i = Z * (W * exchangeMatrix q S i) := mul_assoc _ _ _
    _ = Z * (exchangeMatrix q S i * W) := by rw [hW i hi]
    _ = (Z * exchangeMatrix q S i) * W := (mul_assoc _ _ _).symm
    _ = (exchangeMatrix q S i * Z) * W := by rw [hZ i hi]
    _ = exchangeMatrix q S i * (Z * W) := mul_assoc _ _ _

theorem ExchangeCompatible.one (q : R) (S : Finset V) :
    ExchangeCompatible q (1 : Kernel R S) := by
  classical
  rw [exchangeCompatible_iff_commute]
  intro i hi
  simp

theorem ExchangeCompatible.list_prod (q : R) {S : Finset V} (L : List (Kernel R S))
    (hL : ∀ Z ∈ L, ExchangeCompatible q Z) : ExchangeCompatible q L.prod := by
  classical
  induction L with
  | nil => exact ExchangeCompatible.one q S
  | cons Z L ih =>
    exact (hL Z (by simp)).mul (ih (fun W hW => hL W (by simp [hW])))

end VerticalStripLLT.CyclicHessenberg
