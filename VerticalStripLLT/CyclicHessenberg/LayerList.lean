import VerticalStripLLT.CyclicHessenberg.LayerExchangeCounts

/-! List forms of the original layer conditions, for an explicit all-spectator exchange proof. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V R : Type*} [LinearOrder V]

/-- Later vertices contributing to the ascent count of one strand. -/
def spectatorCount (a C : V) (l : List V) : ℕ :=
  (l.filter fun v => decide (a < v ∧ v ≤ C)).length

@[simp] theorem spectatorCount_nil (a C : V) : spectatorCount a C [] = 0 := rfl

theorem spectatorCount_cons (a C b : V) (l : List V) :
    spectatorCount a C (b :: l) =
      (if a < b ∧ b ≤ C then 1 else 0) + spectatorCount a C l := by
  by_cases hb : a < b ∧ b ≤ C <;> simp [spectatorCount, hb, Nat.add_comm]

theorem spectatorCount_perm (a C : V) {l u : List V} (h : l.Perm u) :
    spectatorCount a C l = spectatorCount a C u :=
  (h.filter _).length_eq

theorem spectatorCount_pair_swap {a b C D : V} (hab : a < b) (hbC : b ≤ C)
    (hCD : C ≤ D) (l : List V) :
    spectatorCount a C l + spectatorCount b D l =
      spectatorCount b C l + spectatorCount a D l := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    simp only [spectatorCount_cons]
    have hh := laterSpectatorIndicatorSwap (v := v) hab hbC hCD
    lia

def layerListFeasible (h : V → V) : List V → List V → Prop
  | [], [] => True
  | a :: l, c :: u => a ≤ h c ∧ layerListFeasible h l u
  | _, _ => False

instance layerListFeasibleDecidable (h : V → V) (l u : List V) :
    Decidable (layerListFeasible h l u) := by
  induction l generalizing u with
  | nil => cases u with
    | nil => exact inferInstanceAs (Decidable True)
    | cons c u => exact inferInstanceAs (Decidable False)
  | cons a l ih => cases u with
    | nil => exact inferInstanceAs (Decidable False)
    | cons c u => exact @instDecidableAnd _ _ inferInstance (ih u)

/-- Count each strand against all later row vertices, then continue on the tails. -/
def layerListAscentCount (h : V → V) : List V → List V → ℕ
  | a :: l, c :: u => spectatorCount a (h c) l + layerListAscentCount h l u
  | _, _ => 0

noncomputable def layerListWeight [CommSemiring R] (h : V → V) (q : R)
    (l u : List V) : R :=
  if layerListFeasible h l u then (1 + q) ^ layerListAscentCount h l u else 0

theorem layerListWeight_cons [CommSemiring R] (h : V → V) (q : R)
    (a c : V) (l u : List V) :
    layerListWeight h q (a :: l) (c :: u) =
      if a ≤ h c then (1 + q) ^ spectatorCount a (h c) l * layerListWeight h q l u
        else 0 := by
  by_cases ha : a ≤ h c <;> by_cases hl : layerListFeasible h l u
  all_goals simp [layerListWeight, layerListFeasible, layerListAscentCount, ha, hl, pow_add]

/-- The four local entries include all later spectators and their independent endpoints. -/
theorem layerListWeight_pair_exchange [CommSemiring R] (h : V → V) (hm : Monotone h)
    (q : R) (a b c d : V) (hab : a < b) (hcd : c < d) (σ σ' : List V) :
    layerListWeight h q ([a, b] ++ σ) ([d, c] ++ σ') =
        (1 + q) * layerListWeight h q ([b, a] ++ σ) ([c, d] ++ σ') ∧
      layerListWeight h q ([a, b] ++ σ) ([c, d] ++ σ') =
        layerListWeight h q ([b, a] ++ σ) ([d, c] ++ σ') +
          q * layerListWeight h q ([b, a] ++ σ) ([c, d] ++ σ') := by
  have hCD : h c ≤ h d := hm hcd.le
  have hba : ¬ b < a := not_lt.mpr hab.le
  by_cases ht : layerListFeasible h σ σ'
  · by_cases hbC : b ≤ h c
    · have haC := hab.le.trans hbC
      have hbD := hbC.trans hCD
      have haD := haC.trans hCD
      have hs := spectatorCount_pair_swap hab hbC hCD σ
      let N := spectatorCount b (h c) σ + spectatorCount a (h d) σ +
        layerListAscentCount h σ σ'
      have hA : layerListAscentCount h (a :: b :: σ) (c :: d :: σ') = N + 1 := by
        simp only [layerListAscentCount, spectatorCount_cons, hab, hbC, and_self,
          ite_true]
        dsimp [N]
        lia
      have hB : layerListAscentCount h (b :: a :: σ) (c :: d :: σ') = N := by
        simp only [layerListAscentCount, spectatorCount_cons, hba, false_and,
          ite_false, zero_add]
        simp [N, Nat.add_assoc]
      have hC : layerListAscentCount h (a :: b :: σ) (d :: c :: σ') = N + 1 := by
        simp only [layerListAscentCount, spectatorCount_cons, hab, hbD, and_self, ite_true]
        dsimp [N]
        lia
      have hD : layerListAscentCount h (b :: a :: σ) (d :: c :: σ') = N := by
        simp only [layerListAscentCount, spectatorCount_cons, hba, false_and, ite_false, zero_add]
        dsimp [N]
        lia
      simp only [List.cons_append, List.nil_append, layerListWeight, layerListFeasible,
        haC, haD, hbC, hbD, ht, and_self, ite_true, hA, hB, hC, hD, pow_succ]
      constructor <;> ring
    · have hcross : ¬ (b ≤ h c ∧ a ≤ h d ∧ layerListFeasible h σ σ') := by simp [hbC]
      have hcross' : ¬ (a ≤ h d ∧ b ≤ h c ∧ layerListFeasible h σ σ') := by simp [hbC]
      have hcount : layerListAscentCount h (a :: b :: σ) (c :: d :: σ') =
          layerListAscentCount h (b :: a :: σ) (d :: c :: σ') := by
        simp only [layerListAscentCount, spectatorCount_cons, hbC, hba, and_false,
          false_and, ite_false, zero_add]
        lia
      simp only [List.cons_append, List.nil_append, layerListWeight, layerListFeasible,
        ite_eq_right hcross, ite_eq_right hcross', mul_zero, add_zero, hcount]
      constructor
      · trivial
      · congr 1
        apply propext
        tauto
  · simp [layerListWeight, layerListFeasible, ht]

/-- Earlier strands see the same unordered row pair, so arbitrary prefixes preserve exchange. -/
theorem layerListWeight_exchangeCompatible [CommSemiring R] (h : V → V)
    (hm : Monotone h) (q : R) : ListExchangeCompatible q (layerListWeight h q) := by
  intro ρ σ ρ' σ' a b c d hlen hab hcd
  induction ρ generalizing ρ' with
  | nil =>
    have hnil : ρ' = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ρ'
    exact layerListWeight_pair_exchange h hm q a b c d hab hcd σ σ'
  | cons x ρ ih =>
    cases ρ' with
    | nil => simp at hlen
    | cons y ρ' =>
      have htail := ih ρ' (Nat.succ.inj hlen)
      have hperm : (ρ ++ [a, b] ++ σ).Perm (ρ ++ [b, a] ++ σ) :=
        ((List.Perm.swap b a []).append_left ρ).append_right σ
      have hs := spectatorCount_perm x (h y) hperm
      simp only [List.cons_append, layerListWeight_cons]
      by_cases hxy : x ≤ h y
      · simp only [ite_eq_left hxy, ← hs]
        rw [htail.1, htail.2]
        constructor <;> ring
      · simp only [ite_eq_right hxy, mul_zero, add_zero, and_self]

end VerticalStripLLT.CyclicHessenberg
