import VerticalStripLLT.Circular.PairedSwap
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Relator

/-! Conjugation for exchanging two parallel directed chains. -/

namespace VerticalStripLLT.Circular

variable {V : Type*}

/-- Replace the two endpoint edges of the `p` chain by the corresponding edges of `q`. -/
def neutralExchangeRelation (R : V → V → Prop) {k : ℕ} (a z : V)
    (p q : Fin (k + 1) → V) : V → V → Prop := fun u v =>
  (R u v ∧ ¬ (u = a ∧ v = p 0) ∧ ¬ (u = p (Fin.last k) ∧ v = z)) ∨
    (u = a ∧ v = q 0) ∨ (u = q (Fin.last k) ∧ v = z)

private theorem pairedSwap_involutive {I V : Type*} (p q : I → V)
    (hp : Function.Injective p) (hq : Function.Injective q) (hpq : ∀ i j, p i ≠ q j) (v : V) :
    pairedSwap p q hp hq hpq (pairedSwap p q hp hq hpq v) = v := by
  classical
  by_cases hpv : ∃ i, v = p i
  · obtain ⟨i, rfl⟩ := hpv
    rw [pairedSwap_left, pairedSwap_right]
  · by_cases hqv : ∃ i, v = q i
    · obtain ⟨i, rfl⟩ := hqv
      rw [pairedSwap_right, pairedSwap_left]
    · have hv := pairedSwap_fixed p q hp hq hpq v
        (fun i h => hpv ⟨i, h⟩) (fun i h => hqv ⟨i, h⟩)
      rw [hv, hv]

private theorem out_p {k : ℕ} (R : V → V → Prop) (hright : Relator.RightUnique R)
    (p : Fin (k + 1) → V) (z : V) (hpend : R (p (Fin.last k)) z)
    (hchain : ∀ i : Fin k, R (p i.castSucc) (p i.succ)) {i : Fin (k + 1)} {v : V}
    (h : R (p i) v) :
    (i = Fin.last k ∧ v = z) ∨ ∃ j : Fin k, i = j.castSucc ∧ v = p j.succ := by
  revert h
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro h; exact Or.inl ⟨rfl, hright h hpend⟩
  · intro h; exact Or.inr ⟨j, rfl, hright h (hchain j)⟩

private theorem out_q {k : ℕ} (R : V → V → Prop) (hright : Relator.RightUnique R)
    (q : Fin (k + 1) → V) (hqlast : ∀ v, ¬ R (q (Fin.last k)) v)
    (hchain : ∀ i : Fin k, R (q i.castSucc) (q i.succ)) {i : Fin (k + 1)} {v : V}
    (h : R (q i) v) : ∃ j : Fin k, i = j.castSucc ∧ v = q j.succ := by
  revert h
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro h; exact (hqlast v h).elim
  · intro h; exact ⟨j, rfl, hright h (hchain j)⟩

private theorem in_p {k : ℕ} (R : V → V → Prop) (hleft : Relator.LeftUnique R)
    (a : V) (p : Fin (k + 1) → V) (hstart : R a (p 0))
    (hchain : ∀ i : Fin k, R (p i.castSucc) (p i.succ)) {u : V} {i : Fin (k + 1)}
    (h : R u (p i)) :
    (i = 0 ∧ u = a) ∨ ∃ j : Fin k, i = j.succ ∧ u = p j.castSucc := by
  revert h
  refine Fin.cases ?_ (fun j => ?_) i
  · intro h; exact Or.inl ⟨rfl, hleft h hstart⟩
  · intro h; exact Or.inr ⟨j, rfl, hleft h (hchain j)⟩

private theorem in_q {k : ℕ} (R : V → V → Prop) (hleft : Relator.LeftUnique R)
    (q : Fin (k + 1) → V) (hqzero : ∀ u, ¬ R u (q 0))
    (hchain : ∀ i : Fin k, R (q i.castSucc) (q i.succ)) {u : V} {i : Fin (k + 1)}
    (h : R u (q i)) : ∃ j : Fin k, i = j.succ ∧ u = q j.castSucc := by
  revert h
  refine Fin.cases ?_ (fun j => ?_) i
  · intro h; exact (hqzero u h).elim
  · intro h; exact ⟨j, rfl, hleft h (hchain j)⟩

/-- Every source edge is an exchanged endpoint edge, an internal chain edge, or exterior. -/
theorem neutralExchange_source_edge_cases {k : ℕ} (R : V → V → Prop)
    (hleft : Relator.LeftUnique R) (hright : Relator.RightUnique R)
    (a z : V) (p q : Fin (k + 1) → V)
    (hpstart : R a (p 0)) (hpend : R (p (Fin.last k)) z)
    (hpchain : ∀ i : Fin k, R (p i.castSucc) (p i.succ))
    (hqchain : ∀ i : Fin k, R (q i.castSucc) (q i.succ))
    (hqzero : ∀ u, ¬ R u (q 0)) (hqlast : ∀ u, ¬ R (q (Fin.last k)) u)
    {u v : V} (huv : R u v) :
    (u = a ∧ v = p 0) ∨ (u = p (Fin.last k) ∧ v = z) ∨
      (∃ i : Fin k, u = p i.castSucc ∧ v = p i.succ) ∨
      (∃ i : Fin k, u = q i.castSucc ∧ v = q i.succ) ∨
      ((∀ i, u ≠ p i) ∧ (∀ i, u ≠ q i) ∧
        (∀ i, v ≠ p i) ∧ ∀ i, v ≠ q i) := by
  classical
  by_cases hup : ∃ i, u = p i
  · obtain ⟨i, rfl⟩ := hup
    rcases out_p R hright p z hpend hpchain huv with hlast | ⟨j, hij, hv⟩
    · exact Or.inr (Or.inl ⟨congrArg p hlast.1, hlast.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨j, congrArg p hij, hv⟩))
  · by_cases huq : ∃ i, u = q i
    · obtain ⟨i, rfl⟩ := huq
      obtain ⟨j, hij, hv⟩ := out_q R hright q hqlast hqchain huv
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, congrArg q hij, hv⟩)))
    · by_cases hvp : ∃ i, v = p i
      · obtain ⟨i, rfl⟩ := hvp
        rcases in_p R hleft a p hpstart hpchain huv with hzero | ⟨j, hij, hu⟩
        · exact Or.inl ⟨hzero.2, congrArg p hzero.1⟩
        · exact (hup ⟨j.castSucc, hu⟩).elim
      · by_cases hvq : ∃ i, v = q i
        · obtain ⟨i, rfl⟩ := hvq
          obtain ⟨j, hij, hu⟩ := in_q R hleft q hqzero hqchain huv
          exact (huq ⟨j.castSucc, hu⟩).elim
        · right
          right
          right
          right
          exact ⟨(fun i h => hup ⟨i, h⟩), (fun i h => huq ⟨i, h⟩),
            (fun i h => hvp ⟨i, h⟩), fun i h => hvq ⟨i, h⟩⟩

/-- The paired swap conjugates the full parallel-chain exchange. -/
theorem neutralExchange_conjugates {k : ℕ} (R : V → V → Prop)
    (hleft : Relator.LeftUnique R) (hright : Relator.RightUnique R)
    (a z : V) (p q : Fin (k + 1) → V) (hp : Function.Injective p)
    (hq : Function.Injective q) (hpq : ∀ i j, p i ≠ q j)
    (haP : ∀ i, a ≠ p i) (haQ : ∀ i, a ≠ q i)
    (hzP : ∀ i, z ≠ p i) (hzQ : ∀ i, z ≠ q i)
    (hpstart : R a (p 0)) (hpend : R (p (Fin.last k)) z)
    (hpchain : ∀ i : Fin k, R (p i.castSucc) (p i.succ))
    (hqchain : ∀ i : Fin k, R (q i.castSucc) (q i.succ))
    (hqzero : ∀ u, ¬ R u (q 0)) (hqlast : ∀ u, ¬ R (q (Fin.last k)) u) (u v : V) :
    R u v ↔ neutralExchangeRelation R a z p q
      (pairedSwap p q hp hq hpq u) (pairedSwap p q hp hq hpq v) := by
  classical
  let σ := pairedSwap p q hp hq hpq
  have hσa : σ a = a := pairedSwap_fixed p q hp hq hpq a haP haQ
  have hσz : σ z = z := pairedSwap_fixed p q hp hq hpq z hzP hzQ
  have hreg : ∀ {x y : V}, R x y →
      ¬ (x = a ∧ y = p 0) → ¬ (x = p (Fin.last k) ∧ y = z) → R (σ x) (σ y) := by
    intro x y hxy hstart hend
    rcases neutralExchange_source_edge_cases R hleft hright a z p q hpstart hpend
      hpchain hqchain hqzero hqlast hxy with h | h | h | h | h
    · exact (hstart h).elim
    · exact (hend h).elim
    · obtain ⟨i, rfl, rfl⟩ := h
      simpa only [σ, pairedSwap_left] using hqchain i
    · obtain ⟨i, rfl, rfl⟩ := h
      simpa only [σ, pairedSwap_right] using hpchain i
    · rw [show σ x = x from pairedSwap_fixed p q hp hq hpq x h.1 h.2.1,
        show σ y = y from pairedSwap_fixed p q hp hq hpq y h.2.2.1 h.2.2.2]
      exact hxy
  have hinv (x : V) : σ (σ x) = x := pairedSwap_involutive p q hp hq hpq x
  change R u v ↔ (R (σ u) (σ v) ∧ ¬ (σ u = a ∧ σ v = p 0) ∧
    ¬ (σ u = p (Fin.last k) ∧ σ v = z)) ∨
    (σ u = a ∧ σ v = q 0) ∨ (σ u = q (Fin.last k) ∧ σ v = z)
  constructor
  · intro huv
    by_cases hstart' : u = a ∧ v = p 0
    · obtain ⟨rfl, rfl⟩ := hstart'
      exact Or.inr (Or.inl ⟨hσa, pairedSwap_left p q hp hq hpq 0⟩)
    · by_cases hend' : u = p (Fin.last k) ∧ v = z
      · obtain ⟨rfl, rfl⟩ := hend'
        exact Or.inr (Or.inr ⟨pairedSwap_left p q hp hq hpq _, hσz⟩)
      · refine Or.inl ⟨hreg huv hstart' hend', ?_, ?_⟩
        · rintro ⟨hu, hv⟩
          have hu' : u = a := σ.injective (hu.trans hσa.symm)
          have hv' : v = q 0 := σ.injective
            (hv.trans (pairedSwap_right p q hp hq hpq 0).symm)
          exact hqzero a (hu' ▸ hv' ▸ huv)
        · rintro ⟨hu, hv⟩
          have hu' : u = q (Fin.last k) := σ.injective
            (hu.trans (pairedSwap_right p q hp hq hpq _).symm)
          have hv' : v = z := σ.injective (hv.trans hσz.symm)
          exact hqlast z (hu' ▸ hv' ▸ huv)
  · rintro (⟨huv, hstart', hend'⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩)
    · simpa only [hinv] using hreg huv hstart' hend'
    · have hu' : u = a := σ.injective (hu.trans hσa.symm)
      have hv' : v = p 0 := σ.injective
        (hv.trans (pairedSwap_left p q hp hq hpq 0).symm)
      exact hu' ▸ hv' ▸ hpstart
    · have hu' : u = p (Fin.last k) := σ.injective
        (hu.trans (pairedSwap_left p q hp hq hpq _).symm)
      have hv' : v = z := σ.injective (hv.trans hσz.symm)
      exact hu' ▸ hv' ▸ hpend

end VerticalStripLLT.Circular
