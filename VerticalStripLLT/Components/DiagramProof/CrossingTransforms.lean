import VerticalStripLLT.Components.DiagramProof.RelationExchange

/-! Endpoint facts for preparing the crossing slide. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V : Type*} [LinearOrder V]

theorem outgoingSweepRelation_no_earlier (R : V → V → Prop) {a b c w : V}
    (hwb : w < b) : ¬ outgoingSweepRelation R a b c a w := by
  simp only [outgoingSweepRelation, lt_self_iff_false, false_and, true_and, hwb,
    not_true_eq_false, and_false, or_self, not_false_eq_true]

theorem incomingSweepRelation_no_later (R : V → V → Prop) {b c d w : V}
    (hcw : c < w) : ¬ incomingSweepRelation R b c d w d := by
  rw [incomingSweepRelation_iff]
  simp only [lt_self_iff_false, false_and, true_and, hcw, not_true_eq_false,
    and_false, or_self, not_false_eq_true]

theorem outgoingSweepRelation_at_boundary (R : V → V → Prop) (a b c : V) :
    outgoingSweepRelation R a b c a b ↔ R a b := by
  simp only [outgoingSweepRelation, lt_self_iff_false, false_and, and_false,
    false_or, not_false_eq_true, and_true]

theorem incomingSweepRelation_at_boundary (R : V → V → Prop) (b c d : V) :
    incomingSweepRelation R b c d c d ↔ R c d := by
  rw [incomingSweepRelation_iff]
  simp only [lt_self_iff_false, false_and, and_false, false_or,
    not_false_eq_true, and_true]

end VerticalStripLLT.Circular.DiagramProof
