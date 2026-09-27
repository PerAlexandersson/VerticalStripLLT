import VerticalStripLLT.Components.GainCoefficient
import Mathlib.Data.Setoid.Basic

/-!
# Transport of contracted coefficients across equal weak partitions

The contraction factors through its weak-component setoid. Equality of those
setoids therefore transports the contracted cycle tests and component counts
without choosing representatives or transporting individual edge walks.
-/

namespace VerticalStripLLT.Components.GainData

open OrderedPartitions

noncomputable section

variable {V E : Type*} [DecidableEq E] (G : GainData V E)

/-- Quotient endpoints by a given setoid, retaining every edge and its adjusted gain. -/
abbrev quotientGain (s : Setoid V) (p : V → ℤ) : GainData (Quotient s) E where
  tail e := Quotient.mk s (G.tail e)
  head e := Quotient.mk s (G.head e)
  gain e := G.gain e - (p (G.head e) - p (G.tail e))

theorem contraction_eq_quotientGain (F : Finset E) (p : V → ℤ) :
    G.contraction F p =
      G.quotientGain (Relation.EqvGen.setoid (G.selectedRelation F)) p := rfl

/-- Pointwise equality of weak connectivity identifies the actual quotient setoids. -/
theorem weakSetoid_eq_of_weakClosure {F F' : Finset E}
    (hweak : ∀ x y, Relation.EqvGen (G.selectedRelation F) x y ↔
      Relation.EqvGen (G.selectedRelation F') x y) :
    Relation.EqvGen.setoid (G.selectedRelation F) =
      Relation.EqvGen.setoid (G.selectedRelation F') :=
  Setoid.ext hweak

theorem weakComponentCount_eq_of_weakClosure {F F' : Finset E}
    (hweak : ∀ x y, Relation.EqvGen (G.selectedRelation F) x y ↔
      Relation.EqvGen (G.selectedRelation F') x y) :
    weakComponentCount (G.selectedRelation F) =
      weakComponentCount (G.selectedRelation F') := by
  change Nat.card (Quotient (Relation.EqvGen.setoid (G.selectedRelation F))) =
    Nat.card (Quotient (Relation.EqvGen.setoid (G.selectedRelation F')))
  rw [G.weakSetoid_eq_of_weakClosure hweak]

/-- Negative cycle gains depend only on the contracted weak partition and common potential. -/
theorem contraction_simpleCyclesNegative_iff_of_weakClosure {F F' : Finset E}
    (p : V → ℤ)
    (hweak : ∀ x y, Relation.EqvGen (G.selectedRelation F) x y ↔
      Relation.EqvGen (G.selectedRelation F') x y) (A : Finset E) :
    (G.contraction F p).SimpleCyclesNegative A ↔
      (G.contraction F' p).SimpleCyclesNegative A := by
  change (G.quotientGain
      (Relation.EqvGen.setoid (G.selectedRelation F)) p).SimpleCyclesNegative A ↔
    (G.quotientGain
      (Relation.EqvGen.setoid (G.selectedRelation F')) p).SimpleCyclesNegative A
  rw [G.weakSetoid_eq_of_weakClosure hweak]

theorem contraction_totallyCyclic_iff_of_weakClosure {F F' : Finset E}
    (p : V → ℤ)
    (hweak : ∀ x y, Relation.EqvGen (G.selectedRelation F) x y ↔
      Relation.EqvGen (G.selectedRelation F') x y) (A : Finset E) :
    TotallyCyclic ((G.contraction F p).selectedRelation A) ↔
      TotallyCyclic ((G.contraction F' p).selectedRelation A) := by
  change TotallyCyclic ((G.quotientGain
      (Relation.EqvGen.setoid (G.selectedRelation F)) p).selectedRelation A) ↔
    TotallyCyclic ((G.quotientGain
      (Relation.EqvGen.setoid (G.selectedRelation F')) p).selectedRelation A)
  rw [G.weakSetoid_eq_of_weakClosure hweak]

theorem contraction_weakComponentCount_eq_of_weakClosure {F F' : Finset E}
    (p : V → ℤ)
    (hweak : ∀ x y, Relation.EqvGen (G.selectedRelation F) x y ↔
      Relation.EqvGen (G.selectedRelation F') x y) (A : Finset E) :
    weakComponentCount ((G.contraction F p).selectedRelation A) =
      weakComponentCount ((G.contraction F' p).selectedRelation A) := by
  change weakComponentCount ((G.quotientGain
      (Relation.EqvGen.setoid (G.selectedRelation F)) p).selectedRelation A) =
    weakComponentCount ((G.quotientGain
      (Relation.EqvGen.setoid (G.selectedRelation F')) p).selectedRelation A)
  rw [G.weakSetoid_eq_of_weakClosure hweak]

/-- Equal tight weak partitions and equal residual edges preserve the companion coefficient.
The two tight sets may differ, but the same integer potential realizes both. -/
theorem coefficient_eq_of_common_potential {R R' F F' : Finset E} {p : V → ℤ}
    (hFR : F ⊆ R) (hF'R' : F' ⊆ R')
    (hp : G.BalancedPotential F p) (hp' : G.BalancedPotential F' p)
    (hweak : ∀ x y, Relation.EqvGen (G.selectedRelation F) x y ↔
      Relation.EqvGen (G.selectedRelation F') x y)
    (hresidual : R \ F = R' \ F') :
    G.coefficient R F = G.coefficient R' F' := by
  rw [G.coefficient_eq_contraction hp hFR, G.coefficient_eq_contraction hp' hF'R']
  rw [hresidual, G.weakComponentCount_eq_of_weakClosure hweak,
    G.contraction_simpleCyclesNegative_iff_of_weakClosure p hweak (R' \ F'),
    G.contraction_totallyCyclic_iff_of_weakClosure p hweak (R' \ F'),
    G.contraction_weakComponentCount_eq_of_weakClosure p hweak (R' \ F')]

end

end VerticalStripLLT.Components.GainData
