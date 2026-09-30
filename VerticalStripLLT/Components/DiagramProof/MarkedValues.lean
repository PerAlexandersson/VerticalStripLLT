import VerticalStripLLT.Components.DiagramProof.Basic
import VerticalStripLLT.Components.SelectedColoringSum
import VerticalStripLLT.Circular.RootedChainCertificate
import VerticalStripLLT.Circular.HRVEvaluation
import VerticalStripLLT.Circular.ComponentSemantics

/-!
# Marked coloring values and their actual semantics

K uses the selected relation. E uses the increasing order inside each actual
HRV fibre. This auxiliary relation need not be a natural diagram. The endpoint
is explicit; right-marked applications choose the greatest vertex.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Circular.DiagramProof

open Classical
open scoped BigOperators

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- Colorings strictly increasing on an arbitrary finite relation. -/
def relationValue (R : Fin n → Fin n → Prop) (m : ℕ) : XPoly m :=
  ∑ c : Fin n → Fin m,
    if ∀ u v, R u v → c u < c v then EdgeData.monomial c else 0

/-- Fix the color of a specified endpoint. -/
def markedRelationValue (R : Fin n → Fin n → Prop) (v : Fin n)
    (m : ℕ) (β : Fin m) : XPoly m :=
  ∑ c : Fin n → Fin m,
    if c v = β ∧ ∀ u w, R u w → c u < c w then EdgeData.monomial c else 0

/-- The strict order within each fibre, including all transitive comparisons. -/
def fibreRelation (H : Fin n → Fin n) (u v : Fin n) : Prop :=
  u < v ∧ H u = H v

def markedK (θ : Orientation D) (v : Fin n) (m : ℕ) (β : Fin m) : XPoly m :=
  markedRelationValue (D.edgeData.selected θ.val) v m β

def markedE (θ : Orientation D) (v : Fin n) (m : ℕ) (β : Fin m) : XPoly m :=
  markedRelationValue (fibreRelation θ.hrv) v m β

theorem sum_markedRelationValue (R : Fin n → Fin n → Prop) (v : Fin n) (m : ℕ) :
    ∑ β : Fin m, markedRelationValue R v m β = relationValue R m := by
  unfold markedRelationValue relationValue
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : ∀ u w, R u w → c u < c w
  · rw [ite_eq_left hc]
    calc
      _ = ∑ β : Fin m, if c v = β then EdgeData.monomial c else 0 := by
        apply Finset.sum_congr rfl
        intro β _
        by_cases hβ : c v = β
        · rw [ite_eq_left ⟨hβ, hc⟩, ite_eq_left hβ]
        · rw [ite_eq_right (fun h => hβ h.1), ite_eq_right hβ]
      _ = _ := by simp
  · simp only [hc, and_false, ite_false, Finset.sum_const_zero]

theorem relationValue_selected (θ : Orientation D) (m : ℕ) :
    relationValue (D.edgeData.selected θ.val) m =
      D.edgeData.strictOrderEnumerator θ.val m := by
  unfold relationValue
  rw [D.edgeData.strictOrderEnumerator_eq_selected_sum]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> rfl

/-- The auxiliary fibre order has the required disjoint-chain semantics. -/
theorem relationValue_fibre (H : Fin n → Fin n) (m : ℕ) :
    relationValue (fibreRelation H) m =
      ∏ r : Fin n, MvPolynomial.esymm (Fin m) Q
        (Finset.univ.filter fun u => H u = r).card := by
  let C := rootedChainColoringCertificate (fibreRelation H) H
    (by
      intro v h
      have hlt : ∀ {u w}, Relation.TransGen (fibreRelation H) u w → u < w := by
        intro u w huw
        induction huw with
        | single h => exact h.1
        | tail _ h ih => exact ih.trans h.1
      exact (lt_irrefl v) (hlt h))
    (fun _ _ h => h.2)
    (by
      intro u v huv
      rcases lt_trichotomy u v with h | rfl | h
      · exact Or.inl (Relation.ReflTransGen.single ⟨h, huv⟩)
      · exact Or.inl Relation.ReflTransGen.refl
      · exact Or.inr (Relation.ReflTransGen.single ⟨h, huv.symm⟩))
  have hsum := rooted_chain_coloring_sum_eq_prod_esymm (fibreRelation H) H C m
  calc
    relationValue (fibreRelation H) m =
        ∑ c : Fin n → Fin m,
          if ∀ u v, fibreRelation H u v → c u < c v then
            ∏ u, MvPolynomial.X (c u) else 0 := by
      unfold relationValue
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> rfl
    _ = ∏ r : Fin n, MvPolynomial.esymm (Fin m) Q
        (Fintype.card {u : Fin n // H u = r}) := by
      convert hsum using 1
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> rfl
    _ = _ := by
      apply Finset.prod_congr rfl
      intro r _
      congr 1
      exact Fintype.card_subtype _

/-- Summing the marked K value recovers the existing strict-coloring polynomial. -/
theorem sum_markedK (θ : Orientation D) (v : Fin n) (m : ℕ) :
    ∑ β : Fin m, markedK θ v m β = D.edgeData.strictOrderEnumerator θ.val m := by
  unfold markedK
  rw [sum_markedRelationValue, relationValue_selected]

/-- Summing marked E recovers the existing evaluated elementary HRV monomial. -/
theorem sum_markedE (θ : Orientation D) (v : Fin n) (m : ℕ) :
    ∑ β : Fin m, markedE θ v m β = evalElementary m θ.hrvMonomial := by
  unfold markedE
  rw [sum_markedRelationValue, relationValue_fibre,
    θ.evalElementary_hrvMonomial]

def componentMarkedK (θ : Orientation D) (v : Fin n) (m : ℕ) (β : Fin m) : XPoly m :=
  ∑ η ∈ flipComponent D θ, markedK η v m β

def componentMarkedE (θ : Orientation D) (v : Fin n) (m : ℕ) (β : Fin m) : XPoly m :=
  ∑ η ∈ flipComponent D θ, markedE η v m β

theorem sum_componentMarkedK (θ : Orientation D) (v : Fin n) (m : ℕ) :
    ∑ β : Fin m, componentMarkedK θ v m β =
      componentStrictEnumerator D θ m := by
  unfold componentMarkedK componentStrictEnumerator
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  exact sum_markedK η v m

theorem sum_componentMarkedE (θ : Orientation D) (v : Fin n) (m : ℕ) :
    ∑ β : Fin m, componentMarkedE θ v m β = evalElementary m (componentHRV D θ) := by
  unfold componentMarkedE componentHRV
  rw [Finset.sum_comm, map_sum]
  apply Finset.sum_congr rfl
  intro η _
  exact sum_markedE η v m

end

end VerticalStripLLT.Circular.DiagramProof
