import VerticalStripLLT.Components.CircularGainData
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Quot

/-!
# Residue-compatible lifts from balanced potentials

An integer balanced potential has a constant residue discrepancy on each weak
block. Subtracting that discrepancy using a chosen block representative gives
actual lifts of the circular vertices, without imposing any bound on their span.
-/

namespace VerticalStripLLT.Circular.Diagram

open Classical

variable {n : ℕ} (D : Diagram n)

/-- Natural length has the expected congruence between the endpoint labels. -/
theorem naturalLength_modEq (e : Edge D.area) :
    Int.ModEq (n : ℤ) ((e.tail.val : ℤ) + e.length.val) (e.head.val : ℤ) := by
  have h := congrArg (fun v : Fin n => (v.val : ℤ))
    (D.residue_add_length e (e.tail.val : ℤ) (Orientation.residue_intCast_eq e.tail))
  rw [D.residue_coe_val] at h
  change ((e.tail.val : ℤ) + e.length.val) % (n : ℤ) = (e.head.val : ℤ) % (n : ℤ)
  calc
    _ = (e.head.val : ℤ) := h
    _ = (e.head.val : ℤ) % (n : ℤ) :=
      (Int.emod_eq_of_lt (Int.natCast_nonneg e.head.val)
        (by exact_mod_cast e.head.isLt)).symm

/-- The potential's discrepancy from the vertex label is constant modulo the period. -/
theorem balancedPotential_modEq_of_weak_connected
    {F : Finset (Edge D.area)} {p : Fin n → ℤ}
    (hp : D.naturalGain.BalancedPotential F p) {x y : Fin n}
    (hxy : Relation.EqvGen (D.naturalGain.selectedRelation F) x y) :
    Int.ModEq (n : ℤ) (p x - (x.val : ℤ)) (p y - (y.val : ℤ)) := by
  induction hxy with
  | rel x y h =>
    obtain ⟨e, he, rfl, rfl⟩ := h
    have hp' : p e.head - p e.tail = (e.length.val : ℤ) := hp e he
    have hm := (Int.ModEq.refl (p e.head)).sub (D.naturalLength_modEq e).symm
    have heq : p e.head - ((e.tail.val : ℤ) + e.length.val) =
        p e.tail - (e.tail.val : ℤ) := by lia
    rw [heq] at hm
    exact hm.symm
  | refl x => exact Int.ModEq.refl _
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-- Every integer balanced potential can be shifted by weak-block constants into actual lifts. -/
theorem exists_residue_balancedPotential
    {F : Finset (Edge D.area)} {p : Fin n → ℤ}
    (hp : D.naturalGain.BalancedPotential F p) :
    ∃ q : Fin n → ℤ, (∀ v, D.residue (q v) = v) ∧
      D.naturalGain.BalancedPotential F q := by
  let r : Fin n → Fin n := fun v => (D.naturalGain.weakBlockMk F v).out
  let q : Fin n → ℤ := fun v => p v + ((r v).val : ℤ) - p (r v)
  have hroot (v : Fin n) :
      Relation.EqvGen (D.naturalGain.selectedRelation F) (r v) v := by
    apply (D.naturalGain.weakBlockMk_eq_iff).mp
    exact Quotient.out_eq (D.naturalGain.weakBlockMk F v)
  refine ⟨q, ?_, ?_⟩
  · intro v
    have hm := D.balancedPotential_modEq_of_weak_connected hp (hroot v)
    have hz : (p v - (v.val : ℤ) - (p (r v) - ((r v).val : ℤ))) % (n : ℤ) = 0 :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hm.symm
    have heq : q v - (v.val : ℤ) =
        p v - (v.val : ℤ) - (p (r v) - ((r v).val : ℤ)) := by
      dsimp [q]
      ring
    have hres : D.residue (q v) = D.residue (v.val : ℤ) := by
      apply (D.residue_eq_iff_mod_sub_zero).mpr
      rw [heq]
      exact hz
    exact hres.trans (Orientation.residue_intCast_eq v)
  · intro e he
    have hr : r e.tail = r e.head :=
      congrArg Quotient.out (D.naturalGain.weakBlockMk_tail_eq_head he)
    have hp' : p e.head - p e.tail = (e.length.val : ℤ) := hp e he
    change q e.head - q e.tail = (e.length.val : ℤ)
    calc
      q e.head - q e.tail = p e.head - p e.tail := by
        dsimp only [q]
        rw [hr]
        ring
      _ = (e.length.val : ℤ) := hp'

/-- Choosing one lift of each residue gives distinct integer positions. -/
theorem injective_of_residue_section {q : Fin n → ℤ}
    (hq : ∀ v, D.residue (q v) = v) : Function.Injective q := by
  intro x y hxy
  have h := congrArg D.residue hxy
  simpa only [hq] using h

/-- Balanced edge sets admit injective residue-compatible integer lifts. -/
theorem exists_injective_balancedLifts {F : Finset (Edge D.area)}
    (hF : D.naturalGain.Balanced F) :
    ∃ q : Fin n → ℤ, (∀ v, D.residue (q v) = v) ∧
      D.naturalGain.BalancedPotential F q ∧ Function.Injective q := by
  obtain ⟨p, hp⟩ := hF
  obtain ⟨q, hq, hbal⟩ := D.exists_residue_balancedPotential hp
  exact ⟨q, hq, hbal, D.injective_of_residue_section hq⟩

end VerticalStripLLT.Circular.Diagram
