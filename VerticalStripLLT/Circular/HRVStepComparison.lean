import VerticalStripLLT.Circular.HRVPotential
import VerticalStripLLT.Circular.FirstBounceOrientationSets
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ}

theorem sub_eq_of_residue_eq (D : Diagram n) {x y x0 y0 : ℤ}
    (hx : D.residue x = D.residue x0) (hy : D.residue y = D.residue y0)
    (h1 : 0 < y - x) (h2 : y - x < n) (h3 : 0 < y0 - x0) (h4 : y0 - x0 < n) :
    y - x = y0 - x0 := by
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period hx
  obtain ⟨l, hl⟩ := D.residue_eq_exists_period hy
  subst hk hl
  have hkl : l = k := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h' : l + 1 ≤ k := by lia
      nlinarith
    · have h' : k + 1 ≤ l := by lia
      nlinarith
  subst hkl
  ring

theorem naturalLift_of_residues (D : Diagram n) {ε : Edge D.area} {x y : ℤ}
    (hx : D.residue x = ε.tail) (hy : D.residue y = ε.head) (h1 : 0 < y - x)
    (h2 : y - x < n) : D.naturalLift ε x y := by
  refine ⟨hx, ?_⟩
  have hb := D.naturalLift_base ε
  have hd := D.sub_eq_of_residue_eq (x0 := (ε.tail.val : ℤ))
    (y0 := (ε.tail.val : ℤ) + ε.length.val) (hx.trans hb.1.symm)
    (hy.trans (D.naturalLift_head hb)) h1 h2
    (by simpa only [add_sub_cancel_left] using
      (show (0 : ℤ) < (ε.length.val : ℤ) by exact_mod_cast ε.length_pos))
    (by simpa only [add_sub_cancel_left] using
      (show (ε.length.val : ℤ) < (n : ℤ) by exact_mod_cast ε.length_lt_n))
  lia

theorem naturalLift_bounds (D : Diagram n) {ε : Edge D.area} {x y : ℤ}
    (h : D.naturalLift ε x y) : 0 < y - x ∧ y - x < n := by
  have hp := ε.length_pos
  have hl := ε.length_lt_n
  rw [h.2]
  constructor <;> lia

theorem liftStep_iff_endpoints (D : Diagram n) (A : Finset (Edge D.area)) (x y : ℤ) :
    D.liftStep A x y ↔ ∃ ε ∈ D.strict ∪ A, ε.tail = D.residue x ∧
      ε.head = D.residue y ∧ 0 < y - x ∧ y - x < n := by
  constructor
  · rintro ⟨ε, hε, hx, hy⟩
    have hnat : D.naturalLift ε x y := ⟨hx, hy⟩
    exact ⟨ε, hε, hx.symm, D.naturalLift_head hnat, D.naturalLift_bounds hnat⟩
  · rintro ⟨ε, hε, hx, hy, h1, h2⟩
    have hnat := D.naturalLift_of_residues hx.symm hy.symm h1 h2
    exact ⟨ε, hε, hnat.1, hnat.2⟩

theorem orientMono_eq_of_transGen {D' : Diagram n} (D : Diagram n)
    (A : Finset (Edge D.area)) (A' : Finset (Edge D'.area))
    (hA : A ⊆ D.edgeData.normalEdges) (hA' : A' ⊆ D'.edgeData.normalEdges)
    (h : ∀ x y, Relation.TransGen (D.liftStep A) x y ↔
      Relation.TransGen (D'.liftStep A') x y) :
    D.orientMono A = D'.orientMono A' := by
  have hadm : D.edgeData.Admissible A ↔ D'.edgeData.Admissible A' := by
    rw [D.admissible_iff_lift, D'.admissible_iff_lift]
    constructor
    · intro H z w hzw
      exact H z w ((h z w).mpr hzw)
    · intro H z w hzw
      exact H z w ((h z w).mp hzw)
  have hrefl : ∀ x y, Relation.ReflTransGen (D.liftStep A) x y ↔
      Relation.ReflTransGen (D'.liftStep A') x y := by
    intro x y
    rw [Relation.reflTransGen_iff_eq_or_transGen,
      Relation.reflTransGen_iff_eq_or_transGen, h]
  apply D.orientMono_eq_of _ _ hA hA'
  · intro had
    refine ⟨hadm.mp had, fun had' => ?_⟩
    let θ : Orientation D := ⟨A, hA, had⟩
    let η : Orientation D' := ⟨A', hA', had'⟩
    have hl : ∀ x, η.liftedHRV x = θ.liftedHRV x := by
      intro x
      apply le_antisymm
      · exact θ.le_liftedHRV_of_reachable
          ((hrefl _ _).mpr (η.liftedHRV_reachable x))
      · exact η.le_liftedHRV_of_reachable
          ((hrefl _ _).mp (θ.liftedHRV_reachable x))
    apply θ.hrvMonomial_conjugate η (Equiv.refl _)
    intro v
    simp only [Equiv.refl_apply]
    change D'.residue (η.liftedHRV _) = D.residue (θ.liftedHRV _)
    rw [hl]
    rfl
  · exact hadm.mpr

end Diagram
end VerticalStripLLT.Circular
