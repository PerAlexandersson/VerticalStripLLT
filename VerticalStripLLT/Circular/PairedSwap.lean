import Mathlib.GroupTheory.Perm.ViaEmbedding

/-! Permutations which exchange two disjoint indexed families of vertices. -/

namespace VerticalStripLLT.Circular

variable {I V : Type*}

private def pairedEmbedding (p q : I → V) (hp : Function.Injective p)
    (hq : Function.Injective q) (hpq : ∀ i j, p i ≠ q j) : Sum I I ↪ V :=
  ⟨Sum.elim p q, by
    intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (hp hxy)
      | inr j => exact (hpq i j hxy).elim
    | inr i =>
      cases y with
      | inl j => exact (hpq j i hxy.symm).elim
      | inr j => exact congrArg Sum.inr (hq hxy)⟩

/-- Exchange `p i` and `q i` simultaneously, fixing every other vertex. -/
noncomputable def pairedSwap (p q : I → V) (hp : Function.Injective p)
    (hq : Function.Injective q) (hpq : ∀ i j, p i ≠ q j) : Equiv.Perm V :=
  Equiv.Perm.viaEmbedding (Equiv.sumComm I I) (pairedEmbedding p q hp hq hpq)

theorem pairedSwap_left (p q : I → V) (hp : Function.Injective p)
    (hq : Function.Injective q) (hpq : ∀ i j, p i ≠ q j) (i : I) :
    pairedSwap p q hp hq hpq (p i) = q i := by
  exact Equiv.Perm.viaEmbedding_apply (Equiv.sumComm I I)
    (pairedEmbedding p q hp hq hpq) (Sum.inl i)

theorem pairedSwap_right (p q : I → V) (hp : Function.Injective p)
    (hq : Function.Injective q) (hpq : ∀ i j, p i ≠ q j) (i : I) :
    pairedSwap p q hp hq hpq (q i) = p i := by
  exact Equiv.Perm.viaEmbedding_apply (Equiv.sumComm I I)
    (pairedEmbedding p q hp hq hpq) (Sum.inr i)

theorem pairedSwap_fixed (p q : I → V) (hp : Function.Injective p)
    (hq : Function.Injective q) (hpq : ∀ i j, p i ≠ q j) (v : V)
    (hpv : ∀ i, v ≠ p i) (hqv : ∀ i, v ≠ q i) :
    pairedSwap p q hp hq hpq v = v := by
  unfold pairedSwap
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i | i, hi⟩
  · change p i = v at hi
    exact hpv i hi.symm
  · change q i = v at hi
    exact hqv i hi.symm

end VerticalStripLLT.Circular
