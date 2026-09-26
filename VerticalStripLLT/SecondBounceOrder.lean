import VerticalStripLLT.SecondBounceTransport
-- Local helper module: VerticalStripLLT.SecondBounceOrder

/-! ## Order facts for the background values `A = h(i)`, `C = h(y)`, `H = h(t)`

Here `A ∈ {i} ∪ (y, ∞)`, `C ∈ {y} ∪ (y, ∞)` and `H > y`, where `y = i + 1`. -/

namespace VerticalStripLLT
namespace BounceHRV

variable {n : ℕ}

/-- Reduce an order statement about `Fin n`, `max` and the swap `(i y)` to `ℕ`. -/
local macro "fin_order" : tactic =>
  `(tactic| (
    simp only [Equiv.swap_apply_def, Fin.le_def, Fin.lt_def, Fin.ext_iff, max_def] at *
    try split_ifs at *
    all_goals lia))

-- The local order tactic consumes hypotheses through `at *`.
set_option linter.unusedVariables false

section OrderFacts

variable {i y A C H : Fin n} (hy : y.val = i.val + 1) (hA : A = i ∨ y < A)
  (hC : C = y ∨ y < C) (hH : y < H)

include hy hA hH in
theorem ord_caseI_swap :
    (Equiv.swap i y C ≤ H ∧ Equiv.swap i y A ≤ H) ↔ (A ≤ H ∧ C ≤ H) := by fin_order

include hy hA hC hH in
theorem ord_swap_CA (hn : ¬(A ≤ H ∧ C ≤ H)) :
    Equiv.swap i y C ≤ Equiv.swap i y A ↔ C ≤ A := by fin_order

include hy hA hC hH in
theorem ord_swap_AC (hn : ¬(A ≤ H ∧ C ≤ H)) :
    Equiv.swap i y A ≤ Equiv.swap i y C ↔ A ≤ C := by fin_order

include hy hA hH in
theorem ord_max_swapA : max (Equiv.swap i y A) H = max A H := by fin_order

include hy hH in
theorem ord_swapC_le : Equiv.swap i y C ≤ max A (max C H) := by fin_order

theorem ord_I_i (hI : A ≤ H ∧ C ≤ H) : max A (max C H) = max A H := by fin_order

theorem ord_I_y (hI : A ≤ H ∧ C ≤ H) : max C H = max A H := by fin_order

theorem ord_CA_i (hn : ¬(A ≤ H ∧ C ≤ H)) (h : C ≤ A) : A = max A H := by fin_order

theorem ord_CA_le (hn : ¬(A ≤ H ∧ C ≤ H)) (h : C ≤ A) : max C H ≤ max A H := by fin_order

theorem ord_AC_y (hn : ¬(A ≤ H ∧ C ≤ H)) (h : A ≤ C) : max C H = C := by fin_order

theorem ord_AC_i (hn : ¬(A ≤ H ∧ C ≤ H)) (h : A ≤ C) : max C H = max A (max C H) := by
  fin_order

include hy hA hH in
theorem ord_IIa_y (hn : ¬(A ≤ H ∧ C ≤ H)) (h : ¬C ≤ A) :
    max (Equiv.swap i y C) (max (Equiv.swap i y A) H) = Equiv.swap i y (max C H) := by
  fin_order

include hy hA hH in
theorem ord_I_swap_i (hI : A ≤ H ∧ C ≤ H) :
    max (Equiv.swap i y A) H = max A (max C H) := by fin_order

include hy hA hH in
theorem ord_IIb_swap_i (hn : ¬(A ≤ H ∧ C ≤ H)) (h : ¬A ≤ C) :
    max (Equiv.swap i y A) H = max A (max C H) := by fin_order

end OrderFacts

end BounceHRV
end VerticalStripLLT
