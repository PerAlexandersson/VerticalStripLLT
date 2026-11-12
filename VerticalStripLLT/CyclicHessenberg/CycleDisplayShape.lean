import VerticalStripLLT.CyclicHessenberg.CycleDisplay
import Mathlib.Data.Finsupp.Weight

/-! Shape statistics and the elementary monomial of a cycle display. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V : Type*} [LinearOrder V]

namespace CycleDisplay

private theorem sourceWord_length_blocks (B : List (V × List V)) :
    (B.map fun b => b.2.length + 1).sum = (cycleSourceWord B).length := by
  induction B with
  | nil => rfl
  | cons b B ih =>
      change b.2.length + 1 + (B.map fun b => b.2.length + 1).sum =
        (b.1 :: b.2 ++ cycleSourceWord B).length
      rw [ih, List.length_append, List.length_cons]

private theorem shape_weight_blocks (B : List (V × List V)) :
    Finsupp.weight (fun d : ℕ+ => d.val)
        ((B.map fun b => Finsupp.single (blockSize b) 1).sum) =
      (B.map fun b => (blockSize b).val).sum := by
  induction B with
  | nil => simp
  | cons b B ih =>
      simp only [List.map_cons, List.sum_cons, map_add, Finsupp.weight_single, one_smul, ih]

private theorem shape_degree_blocks (B : List (V × List V)) :
    Finsupp.degree ((B.map fun b => Finsupp.single (blockSize b) 1).sum) =
      B.length := by
  induction B with
  | nil => simp
  | cons b B ih =>
      simp [List.map_cons, List.sum_cons, Finsupp.degree_single, ih, Nat.add_comm]

private theorem elementaryMonomial_blocks (B : List (V × List V)) :
    (B.map fun b => natElementary (blockSize b)).prod =
      MvPolynomial.monomial
        ((B.map fun b => Finsupp.single (blockSize b) 1).sum) 1 := by
  induction B with
  | nil => simp [natElementary]
  | cons b B ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [ih]
      simp only [natElementary, MvPolynomial.X, MvPolynomial.monomial_mul_monomial]
      simp

theorem shape_weight {S : Finset V} (D : CycleDisplay S) :
    D.shape.sum (fun d n => d.val * n) = S.card := by
  rw [← D.source_order.length]
  rw [← sourceWord_length_blocks]
  have hw := shape_weight_blocks D.blocks
  rw [Finsupp.weight_apply] at hw
  change ((D.blocks.map fun b => Finsupp.single (blockSize b) 1).sum.sum
    fun d n => d.val * n) = (D.blocks.map fun b => b.2.length + 1).sum
  simpa only [smul_eq_mul, mul_comm] using hw

theorem shape_degree {S : Finset V} (D : CycleDisplay S) :
    D.shape.sum (fun _ n => n) = D.count := by
  simpa [shape, count, Finsupp.degree_apply, Finsupp.sum] using
    shape_degree_blocks D.blocks

theorem elementaryMonomial_eq_monomial {S : Finset V} (D : CycleDisplay S) :
    D.elementaryMonomial = MvPolynomial.monomial D.shape 1 := by
  simpa [elementaryMonomial, shape] using elementaryMonomial_blocks D.blocks

end CycleDisplay

end VerticalStripLLT.CyclicHessenberg
