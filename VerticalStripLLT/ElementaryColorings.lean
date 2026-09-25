import VerticalStripLLT.Polynomial
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi

/-! Increasing colorings enumerate the squarefree monomials of an elementary polynomial.

The bijection proof below was supplied in an in-progress Aristotle event for
project `262ce79f-3c8a-4e6a-83f7-6fcf6a6c9eb6`, ported by Luna, and checked
locally with Lean 4.34. See `docs/ARISTOTLE.md` for precise provenance.
-/

namespace VerticalStripLLT

open scoped BigOperators

noncomputable def increasingColoringSum (n m : ℕ) : XPoly m := by
  classical
  exact ∑ c : Fin n → Fin m,
    if StrictMono c then ∏ i, MvPolynomial.X (c i) else 0

/-- Valid also for zero vertices or an empty alphabet. -/
theorem increasingColoringSum_eq_esymm (n m : ℕ) :
    increasingColoringSum n m =
      MvPolynomial.esymm (Fin m) Q n := by
  classical
  rw [MvPolynomial.esymm, increasingColoringSum]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun c _ => Finset.univ.image c) ?_ ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by
      rw [Finset.card_image_of_injective _ hc.injective]
      simp⟩
  · intro c hc c' hc' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hc'
    have hcard : (Finset.univ.image c).card = n := by
      rw [Finset.card_image_of_injective _ hc.injective]
      simp
    have h1 := Finset.orderEmbOfFin_unique hcard (f := c) (by simp) hc
    have h2 := Finset.orderEmbOfFin_unique hcard (f := c') (by simp [h]) hc'
    rw [h1, h2]
  · intro t ht
    rw [Finset.mem_powersetCard] at ht
    refine ⟨fun i => t.orderEmbOfFin ht.2 i, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (t.orderEmbOfFin ht.2).strictMono
    · exact Finset.image_orderEmbOfFin_univ t ht.2
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Finset.prod_image (fun x _ y _ hxy => hc.injective hxy)]

end VerticalStripLLT
