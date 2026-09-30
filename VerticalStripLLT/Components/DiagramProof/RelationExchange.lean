import VerticalStripLLT.Components.DiagramProof.OrderedSweep

/-! Exact endpoint algebra for disjoint exchanges and restoration of crossing sweeps. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V : Type*}

/-- Delete one endpoint pair and insert another. -/
def exchangeRelation (R : V → V → Prop) (a b c d u v : V) : Prop :=
  (u = c ∧ v = d) ∨ (R u v ∧ ¬ (u = a ∧ v = b))

theorem exchangeRelation_inverse (R : V → V → Prop) {a b c d : V}
    (hab : R a b) (hcd : ¬ R c d) (u v : V) :
    exchangeRelation (exchangeRelation R a b c d) c d a b u v ↔ R u v := by
  simp only [exchangeRelation]
  grind

/-- Exchanges commute when neither removes the edge inserted by the other. -/
theorem exchangeRelation_commute (R : V → V → Prop) {a b c d p q r s : V}
    (h₁ : (a, b) ≠ (r, s)) (h₂ : (c, d) ≠ (p, q)) (u v : V) :
    exchangeRelation (exchangeRelation R a b c d) p q r s u v ↔
      exchangeRelation (exchangeRelation R p q r s) a b c d u v := by
  simp only [exchangeRelation]
  grind

theorem exchangeRelation_congr {R S : V → V → Prop} (h : ∀ u v, R u v ↔ S u v)
    (a b c d u v : V) : exchangeRelation R a b c d u v ↔ exchangeRelation S a b c d u v := by
  simp only [exchangeRelation, h]

/-- An exchange depends on the original relation only at the queried pair. -/
theorem exchangeRelation_congr_at {R S : V → V → Prop} {a b c d u v : V}
    (h : R u v ↔ S u v) :
    exchangeRelation R a b c d u v ↔ exchangeRelation S a b c d u v := by
  simp only [exchangeRelation, h]

/-- An edge different from both exchanged pairs is unchanged. -/
theorem exchangeRelation_iff_of_untouched (R : V → V → Prop) {a b c d u v : V}
    (hab : ¬ (u = a ∧ v = b)) (hcd : ¬ (u = c ∧ v = d)) :
    exchangeRelation R a b c d u v ↔ R u v := by
  simp only [exchangeRelation, hcd, false_or, hab, not_false_eq_true, and_true]

variable [LinearOrder V]

/-- The incoming sweep does not affect any edge whose head is at or below its cutoff. -/
theorem incomingSweepRelation_agree_below {R : V → V → Prop} {b c d u v : V}
    (hcd : c < d) (hvc : v ≤ c) : incomingSweepRelation R b c d u v ↔ R u v := by
  have hvd : v ≠ d := (hvc.trans_lt hcd).ne
  have hnot : ¬ c < v := not_lt_of_ge hvc
  rw [incomingSweepRelation_iff]
  simp only [hvd, hnot, false_and, and_false, false_or, not_false_eq_true, and_true]

end VerticalStripLLT.Circular.DiagramProof
