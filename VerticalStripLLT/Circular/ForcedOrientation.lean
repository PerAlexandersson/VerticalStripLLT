import VerticalStripLLT.Circular.FirstBounceOrientationIdentity
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Removing a normal edge whose ascent is already forced by a strict path. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Orientation

variable {n : ℕ} {D : Diagram n}

/-- A strict path dominates the shortest positive lift of the same endpoint pair. -/
theorem liftedHRV_le_of_strict_path (θ : Orientation D) (e : Edge D.area)
    (hpath : Relation.TransGen (D.edgeData.selected ∅) e.tail e.head)
    (z : ℤ) (hz : D.residue z = e.tail) :
    θ.liftedHRV (z + e.length.val) ≤ θ.liftedHRV z := by
  obtain ⟨w, hw, hp⟩ := D.exists_lift_of_transGen_selected hpath z hz
  have hpos := D.transGen_lt hp
  have hr := D.residue_add_length e z hz
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period (hw.trans hr.symm)
  have hn : (0 : ℤ) < n := by exact_mod_cast D.area.positive
  have hel : (e.length.val : ℤ) < n := by exact_mod_cast e.length_lt_n
  have hk0 : 0 ≤ k := by
    by_contra h
    have hneg : k ≤ -1 := by lia
    have hmul : (n : ℤ) * k ≤ -n := by nlinarith
    lia
  have hp' : Relation.TransGen (D.liftStep θ.val) z w := by
    apply Relation.TransGen.mono (fun a b hab => ?_) _ _ hp
    obtain ⟨f, hf, ht, hh⟩ := hab
    refine ⟨f, ?_, ht, hh⟩
    simp only [Finset.union_empty] at hf
    exact Finset.mem_union_left _ hf
  have hle := θ.liftedHRV_le_of_reach hp'.to_reflTransGen
  rw [hk, θ.liftedHRV_translate] at hle
  have hmul : 0 ≤ (n : ℤ) * k := mul_nonneg (le_of_lt hn) hk0
  lia

end Orientation

namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem orientMono_insert_of_strict_path (e : Edge D.area)
    (he : e ∈ D.edgeData.normalEdges)
    (hpath : Relation.TransGen (D.edgeData.selected ∅) e.tail e.head)
    (A : Finset (Edge D.area)) (hA : A ⊆ D.edgeData.normalEdges) :
    D.orientMono (insert e A) = D.orientMono A := by
  by_cases ha : D.edgeData.Admissible A
  · let θ : Orientation D := ⟨A, hA, ha⟩
    rw [D.orientMono_orientation θ]
    apply D.orientMono_noop θ (insert e A) (Finset.insert_subset he hA)
      (Finset.subset_insert _ _)
    intro f hf hnot
    rcases Finset.mem_insert.mp hf with hfe | hf
    · subst f
      refine ⟨(e.tail.val : ℤ), Orientation.residue_intCast_eq e.tail, ?_⟩
      exact θ.liftedHRV_le_of_strict_path e hpath _ (Orientation.residue_intCast_eq e.tail)
    · exact False.elim (hnot hf)
  · rw [D.orientMono_of_not_adm ha, D.orientMono_of_not_adm
      (fun h => ha (D.admissible_mono (Finset.subset_insert _ _) h))]

/-- Exact factorization; the restricted sum is not asserted to be another diagram. -/
theorem shiftedOrientationExpansion_forced_edge (e : Edge D.area)
    (he : e ∈ D.edgeData.normalEdges)
    (hpath : Relation.TransGen (D.edgeData.selected ∅) e.tail e.head) :
    shiftedOrientationExpansion D = MvPolynomial.C (Polynomial.X + 1) *
      ∑ A ∈ (D.edgeData.normalEdges.erase e).powerset,
        MvPolynomial.C (Polynomial.X ^ A.card) * D.orientMono A := by
  rw [D.shiftedOrientationExpansion_eq_sum]
  conv_lhs => rw [← Finset.insert_erase he]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase e D.edgeData.normalEdges)]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have hsub := Finset.mem_powerset.mp hA
  have hAe : e ∉ A := fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
  rw [D.orientMono_insert_of_strict_path e he hpath A
    (hsub.trans (Finset.erase_subset _ _)), Finset.card_insert_of_notMem hAe, pow_succ,
    MvPolynomial.C_mul, MvPolynomial.C_add, MvPolynomial.C_1]
  ring

/-- Selecting a normal edge against a strict path creates a directed cycle. -/
theorem orientMono_insert_of_reverse_strict_path (e : Edge D.area)
    (hpath : Relation.TransGen (D.edgeData.selected ∅) e.head e.tail)
    (A : Finset (Edge D.area)) : D.orientMono (insert e A) = 0 := by
  apply D.orientMono_of_not_adm
  intro ha
  have hp : Relation.TransGen (D.edgeData.selected (insert e A)) e.head e.tail := by
    apply Relation.TransGen.mono (fun u v h => ?_) _ _ hpath
    obtain ⟨f, hf, ht, hh⟩ := h
    refine ⟨f, ?_, ht, hh⟩
    simp only [Finset.union_empty] at hf
    exact Finset.mem_union_left _ hf
  have he : D.edgeData.selected (insert e A) e.tail e.head :=
    ⟨e, Finset.mem_union_right _ (Finset.mem_insert_self _ _), rfl, rfl⟩
  exact ha e.head (hp.tail he)

theorem shiftedOrientationExpansion_descent_edge (e : Edge D.area)
    (he : e ∈ D.edgeData.normalEdges)
    (hpath : Relation.TransGen (D.edgeData.selected ∅) e.head e.tail) :
    shiftedOrientationExpansion D =
      ∑ A ∈ (D.edgeData.normalEdges.erase e).powerset,
        MvPolynomial.C (Polynomial.X ^ A.card) * D.orientMono A := by
  rw [D.shiftedOrientationExpansion_eq_sum]
  conv_lhs => rw [← Finset.insert_erase he]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase e D.edgeData.normalEdges)]
  simp only [D.orientMono_insert_of_reverse_strict_path e hpath,
    mul_zero, Finset.sum_const_zero, add_zero]

end Diagram
end VerticalStripLLT.Circular
