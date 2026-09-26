import VerticalStripLLT.Circular.PeriodicSwapHRV
import VerticalStripLLT.Circular.BoundaryEdges
import VerticalStripLLT.Circular.ShortenStrictPairs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! General tools: lifted acyclicity and potential comparison of circular HRV. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

theorem reflTransGen_firstUse {R R' F : ℤ → ℤ → Prop}
    (hR' : ∀ x y, R' x y → R x y ∨ F x y) {z w : ℤ} (h : Relation.ReflTransGen R' z w) :
    Relation.ReflTransGen R z w ∨
      ∃ c c', Relation.ReflTransGen R z c ∧ F c c' ∧ Relation.ReflTransGen R' c' w := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rename_i b c _
    rcases ih with ih | ⟨c₁, c₂, h1, h2, h3⟩
    · rcases hR' _ _ hstep with hs | hs
      · exact Or.inl (ih.tail hs)
      · exact Or.inr ⟨b, c, ih, hs, Relation.ReflTransGen.refl⟩
    · exact Or.inr ⟨c₁, c₂, h1, h2, h3.tail hstep⟩

namespace Diagram

variable {n : ℕ}

theorem residue_eq_exists_period (D : Diagram n) {x y : ℤ}
    (h : D.residue x = D.residue y) : ∃ k : ℤ, x = y + (n : ℤ) * k := by
  have hmod := (D.residue_eq_iff_mod_sub_zero).mp h
  refine ⟨(x - y) / n, ?_⟩
  have hdiv := Int.mul_ediv_add_emod (x - y) n
  rw [hmod] at hdiv
  linarith

theorem residue_add_length (D : Diagram n) (e : Edge D.area) (z : ℤ)
    (hz : D.residue z = e.tail) : D.residue (z + (e.length.val : ℤ)) = e.head := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [D.residue_coe_val]
  have hz' := congrArg (fun v : Fin n => (v.val : ℤ)) hz
  rw [D.residue_coe_val] at hz'
  have hlenmod : (e.length.val : ℤ) % n = e.length.val :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast e.length_lt_n)
  rw [Int.add_emod, hz', hlenmod]
  exact_mod_cast e.tail_add_length_mod

theorem liftStep_lt (D : Diagram n) {A : Finset (Edge D.area)} {z w : ℤ}
    (h : D.liftStep A z w) : z < w := by
  have := (D.liftStep_bounds h).1
  lia

theorem transGen_lt (D : Diagram n) {A : Finset (Edge D.area)} {z w : ℤ}
    (h : Relation.TransGen (D.liftStep A) z w) : z < w := by
  induction h with
  | single h => exact D.liftStep_lt h
  | tail _ hs ih => exact ih.trans (D.liftStep_lt hs)

theorem transGen_selected_of_lift (D : Diagram n) {A : Finset (Edge D.area)} {z w : ℤ}
    (h : Relation.TransGen (D.liftStep A) z w) :
    Relation.TransGen (D.edgeData.selected A) (D.residue z) (D.residue w) := by
  induction h with
  | single h => exact Relation.TransGen.single (D.liftStep_selected h)
  | tail _ hs ih => exact ih.tail (D.liftStep_selected hs)

theorem exists_lift_of_transGen_selected (D : Diagram n) {A : Finset (Edge D.area)}
    {u v : Fin n} (h : Relation.TransGen (D.edgeData.selected A) u v) :
    ∀ z, D.residue z = u → ∃ w, D.residue w = v ∧
      Relation.TransGen (D.liftStep A) z w := by
  induction h with
  | single h =>
    intro z hz
    rcases h with ⟨e, he, ht, hh⟩
    refine ⟨z + (e.length.val : ℤ), ?_, Relation.TransGen.single ⟨e, he, ?_, rfl⟩⟩
    · rw [D.residue_add_length e z (hz.trans ht.symm)]
      exact hh
    · exact hz.trans ht.symm
  | tail _ hs ih =>
    intro z hz
    obtain ⟨w, hw, hzw⟩ := ih z hz
    rcases hs with ⟨e, he, ht, hh⟩
    refine ⟨w + (e.length.val : ℤ), ?_, hzw.tail ⟨e, he, ?_, rfl⟩⟩
    · rw [D.residue_add_length e w (hw.trans ht.symm)]
      exact hh
    · exact hw.trans ht.symm

theorem admissible_iff_lift (D : Diagram n) (A : Finset (Edge D.area)) :
    D.edgeData.Admissible A ↔
      ∀ z w, Relation.TransGen (D.liftStep A) z w → D.residue z ≠ D.residue w := by
  constructor
  · intro hA z w h hzw
    have hs := D.transGen_selected_of_lift h
    rw [hzw] at hs
    exact hA _ hs
  · intro h v hv
    obtain ⟨w, hw, hzw⟩ := D.exists_lift_of_transGen_selected hv (v.val : ℤ)
      (Orientation.residue_intCast_eq v)
    exact h _ _ hzw ((Orientation.residue_intCast_eq v).trans hw.symm)

theorem admissible_mono (D : Diagram n) {A B : Finset (Edge D.area)} (hAB : A ⊆ B)
    (hB : D.edgeData.Admissible B) : D.edgeData.Admissible A := by
  intro v hv
  apply hB v
  refine Relation.TransGen.mono ?_ _ _ hv
  rintro u w ⟨e, he, ht, hh⟩
  refine ⟨e, ?_, ht, hh⟩
  rcases Finset.mem_union.mp he with h | h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (hAB h)

end Diagram

namespace Orientation

variable {n : ℕ} {D D' : Diagram n}

theorem le_liftedHRV (θ : Orientation D) (x : ℤ) : x ≤ θ.liftedHRV x :=
  z_le_maximum _ _ _

theorem liftedHRV_le_of_reach (θ : Orientation D) {x y : ℤ}
    (h : Relation.ReflTransGen (D.liftStep θ.val) x y) : θ.liftedHRV y ≤ θ.liftedHRV x :=
  θ.le_liftedHRV_of_reachable (h.trans (θ.liftedHRV_reachable y))

theorem liftedHRV_le_of_step (θ : Orientation D) {x y : ℤ}
    (h : D.liftStep θ.val x y) : θ.liftedHRV y ≤ θ.liftedHRV x :=
  θ.liftedHRV_le_of_reach (Relation.ReflTransGen.single h)

theorem no_lifted_cycle (θ : Orientation D) {z w : ℤ}
    (h : Relation.TransGen (D.liftStep θ.val) z w) : D.residue z ≠ D.residue w :=
  (D.admissible_iff_lift θ.val).mp θ.property.2 z w h

theorem potential_le_of_reach (θ : Orientation D) {R : ℤ → ℤ → Prop}
    (hmono : ∀ x y, R x y → θ.liftedHRV y ≤ θ.liftedHRV x) {x y : ℤ}
    (h : Relation.ReflTransGen R x y) : θ.liftedHRV y ≤ θ.liftedHRV x := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact (hmono _ _ hs).trans ih

theorem admissible_of_potential (θ : Orientation D) (A : Finset (Edge D'.area))
    (hmono : ∀ x y, D'.liftStep A x y → θ.liftedHRV y ≤ θ.liftedHRV x) :
    D'.edgeData.Admissible A := by
  rw [D'.admissible_iff_lift]
  intro z w h hzw
  have hlt := D'.transGen_lt h
  obtain ⟨k, hk⟩ := D'.residue_eq_exists_period hzw.symm
  have hle := θ.potential_le_of_reach hmono h.to_reflTransGen
  rw [hk, θ.liftedHRV_translate] at hle
  have hn : (0 : ℤ) < n := by exact_mod_cast D.area.positive
  have hk0 : 0 < (n : ℤ) * k := by lia
  lia

theorem liftedHRV_eq_of_potential (θ : Orientation D) (η : Orientation D')
    (h1 : ∀ x y, D.liftStep θ.val x y → Relation.ReflTransGen (D'.liftStep η.val) x y)
    (hmono : ∀ x y, D'.liftStep η.val x y → θ.liftedHRV y ≤ θ.liftedHRV x) (x : ℤ) :
    η.liftedHRV x = θ.liftedHRV x := by
  apply le_antisymm
  · have h := θ.potential_le_of_reach hmono (η.liftedHRV_reachable x)
    exact (θ.le_liftedHRV _).trans h
  · apply η.le_liftedHRV_of_reachable
    have key : ∀ w, Relation.ReflTransGen (D.liftStep θ.val) x w →
        Relation.ReflTransGen (D'.liftStep η.val) x w := by
      intro w hw
      induction hw with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hs ih => exact ih.trans (h1 _ _ hs)
    exact key _ (θ.liftedHRV_reachable x)

theorem hrvMonomial_eq_of_potential (θ : Orientation D) (η : Orientation D')
    (h1 : ∀ x y, D.liftStep θ.val x y → Relation.ReflTransGen (D'.liftStep η.val) x y)
    (hmono : ∀ x y, D'.liftStep η.val x y → θ.liftedHRV y ≤ θ.liftedHRV x) :
    η.hrvMonomial = θ.hrvMonomial := by
  apply θ.hrvMonomial_conjugate η (Equiv.refl _)
  intro v
  simp only [Equiv.refl_apply]
  unfold hrv
  rw [θ.liftedHRV_eq_of_potential η h1 hmono]
  rfl

theorem liftedHRV_edge_all_lifts (θ : Orientation D) (f : Edge D.area)
    (h : θ.liftedHRV ((f.tail.val : ℤ) + f.length.val) ≤ θ.liftedHRV (f.tail.val : ℤ))
    (x : ℤ) (hx : D.residue x = f.tail) :
    θ.liftedHRV (x + f.length.val) ≤ θ.liftedHRV x := by
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period (hx.trans (residue_intCast_eq f.tail).symm)
  rw [hk, show (f.tail.val : ℤ) + n * k + f.length.val =
    ((f.tail.val : ℤ) + f.length.val) + n * k by ring, θ.liftedHRV_translate,
    θ.liftedHRV_translate]
  lia

end Orientation

end VerticalStripLLT.Circular
