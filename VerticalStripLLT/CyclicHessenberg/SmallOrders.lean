import VerticalStripLLT.CyclicHessenberg.TwoVertexExpansion

set_option autoImplicit false

/-! Explicit finite-order formulas on a two-element support. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V : Type*} [LinearOrder V]

/-- The order listing the two named vertices in increasing display order. -/
def pairForwardOrder (a b : V) (hne : a ≠ b) : Order ({a, b} : Finset V) :=
  ⟨[a, b], by simp [IsOrder, hne]⟩

/-- The order listing the two named vertices in reverse display order. -/
def pairReverseOrder (a b : V) (hne : a ≠ b) : Order ({a, b} : Finset V) :=
  ⟨[b, a], by simp [IsOrder, hne.symm, Finset.pair_comm]⟩

@[simp] theorem pairForwardOrder_val (a b : V) (hne : a ≠ b) :
    (pairForwardOrder a b hne).val = [a, b] := rfl

@[simp] theorem pairReverseOrder_val (a b : V) (hne : a ≠ b) :
    (pairReverseOrder a b hne).val = [b, a] := rfl

/-- Every order of a two-element named support is one of its two list orders. -/
theorem order_pair_val_eq_forward_or_reverse (a b : V) (hne : a ≠ b)
    (σ : Order ({a, b} : Finset V)) : σ.val = [a, b] ∨ σ.val = [b, a] := by
  have hlen : σ.val.length = 2 := by
    simpa [hne] using σ.property.length
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hlen
  have hmem (z : V) (hz : z ∈ σ.val) : z = a ∨ z = b := by
    have hz' : z ∈ ({a, b} : Finset V) := (σ.property.mem_iff z).mp hz
    simpa [Finset.mem_insert, Finset.mem_singleton] using hz'
  have hxmem : x ∈ σ.val := by rw [hxy]; simp
  have hymem : y ∈ σ.val := by rw [hxy]; simp
  rcases hmem x hxmem with hx | hx
  · subst x
    rcases hmem y hymem with hy | hy
    · subst y
      have hnodup := σ.property.1
      simp [hxy] at hnodup
    · subst y
      exact Or.inl hxy
  · subst x
    rcases hmem y hymem with hy | hy
    · subst y
      exact Or.inr hxy
    · subst y
      have hnodup := σ.property.1
      simp [hxy] at hnodup

/-- The finite order sum on two vertices is the sum of its two displayed orders. -/
theorem sum_order_pair {R : Type*} [AddCommMonoid R] (a b : V) (hne : a ≠ b)
    (F : Order ({a, b} : Finset V) → R) :
    (∑ σ : Order ({a, b} : Finset V), F σ) =
      F (pairForwardOrder a b hne) + F (pairReverseOrder a b hne) := by
  classical
  let forward := pairForwardOrder a b hne
  let reverse := pairReverseOrder a b hne
  have hrev : [b, a] ≠ [a, b] := by
    intro h
    have hba : b = a := (List.cons.inj h).1
    exact hne hba.symm
  let e : Order ({a, b} : Finset V) ≃ Bool := {
    toFun σ := if σ.val = [a, b] then false else true
    invFun t := if t then reverse else forward
    left_inv σ := by
      rcases order_pair_val_eq_forward_or_reverse a b hne σ with h | h
      · apply Subtype.ext
        simpa [h, forward]
      · apply Subtype.ext
        simp [h, hrev, reverse]
    right_inv t := by
      cases t <;> simp [forward, reverse, pairForwardOrder, pairReverseOrder, hne, hrev] }
  calc
    (∑ σ : Order ({a, b} : Finset V), F σ) = ∑ t : Bool, F (e.symm t) :=
      (Equiv.sum_comp e.symm F).symm
    _ = F forward + F reverse := by
      simp [e, forward, reverse, add_comm]

end VerticalStripLLT.CyclicHessenberg
