import VerticalStripLLT.Circular.HRVRoots

/-! Transport of actual lifted HRV under a relabeling that preserves the order of sinks. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Orientation

variable {n : ℕ} {D D' : Diagram n}

/-- A lift isomorphism need only preserve the order of sinks to preserve greatest reachability. -/
theorem liftedHRV_conjugate (θ : Orientation D) (η : Orientation D') (σ : ℤ ≃ ℤ)
    (hstep : ∀ x y, D.liftStep θ.val x y ↔ D'.liftStep η.val (σ x) (σ y))
    (horder : ∀ x y, (∀ z, ¬ D.liftStep θ.val x z) →
      (∀ z, ¬ D.liftStep θ.val y z) → x ≤ y → σ x ≤ σ y) (x : ℤ) :
    η.liftedHRV (σ x) = σ (θ.liftedHRV x) := by
  have hf : ∀ a b, Relation.ReflTransGen (D.liftStep θ.val) a b →
      Relation.ReflTransGen (D'.liftStep η.val) (σ a) (σ b) := by
    intro a b h
    exact h.lift σ (fun u v huv => (hstep u v).mp huv)
  have hb : ∀ a b, Relation.ReflTransGen (D'.liftStep η.val) a b →
      Relation.ReflTransGen (D.liftStep θ.val) (σ.symm a) (σ.symm b) := by
    intro a b h
    exact h.lift σ.symm (fun u v huv => (hstep (σ.symm u) (σ.symm v)).mpr
      (by simpa using huv))
  have hback : Relation.ReflTransGen (D.liftStep θ.val) x
      (σ.symm (η.liftedHRV (σ x))) := by
    simpa using hb _ _ (η.liftedHRV_reachable (σ x))
  have hsink : ∀ z, ¬ D.liftStep θ.val (σ.symm (η.liftedHRV (σ x))) z := by
    intro z hz
    apply η.no_liftStep_from_liftedHRV (σ x) (σ z)
    simpa using (hstep _ _).mp hz
  apply le_antisymm
  · simpa using horder _ _ hsink (θ.no_liftStep_from_liftedHRV x)
      (θ.le_liftedHRV_of_reachable hback)
  · exact η.le_liftedHRV_of_reachable (hf _ _ (θ.liftedHRV_reachable x))

/-- Projecting a periodic lift conjugacy gives the corresponding finite HRV conjugacy. -/
theorem hrv_conjugate (θ : Orientation D) (η : Orientation D')
    (σ : ℤ ≃ ℤ) (π : Fin n ≃ Fin n)
    (hres : ∀ x, D'.residue (σ x) = π (D.residue x))
    (hstep : ∀ x y, D.liftStep θ.val x y ↔ D'.liftStep η.val (σ x) (σ y))
    (horder : ∀ x y, (∀ z, ¬ D.liftStep θ.val x z) →
      (∀ z, ¬ D.liftStep θ.val y z) → x ≤ y → σ x ≤ σ y) (v : Fin n) :
    η.hrv (π v) = π (θ.hrv v) := by
  have h := congrArg D'.residue (θ.liftedHRV_conjugate η σ hstep horder (v.val : ℤ))
  rw [η.residue_liftedHRV_eq_hrv, hres, residue_intCast_eq, hres] at h
  exact h

/-- Relabeling both vertices and HRV roots preserves every fiber cardinality. -/
theorem hrvFiber_card_conjugate (θ : Orientation D) (η : Orientation D')
    (π : Fin n ≃ Fin n) (h : ∀ v, η.hrv (π v) = π (θ.hrv v)) (r : Fin n) :
    (Finset.univ.filter fun u => η.hrv u = π r).card =
      (Finset.univ.filter fun u => θ.hrv u = r).card := by
  have hf : (Finset.univ.filter fun u => η.hrv u = π r) =
      (Finset.univ.filter fun u => θ.hrv u = r).map π.toEmbedding := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply]
    constructor
    · intro hu
      refine ⟨π.symm u, ?_, π.apply_symm_apply u⟩
      apply π.injective
      rw [← h, π.apply_symm_apply]
      exact hu
    · rintro ⟨v, hv, rfl⟩
      rw [h, hv]
  rw [hf, Finset.card_map]

theorem hrvMonomial_conjugate (θ : Orientation D) (η : Orientation D')
    (π : Fin n ≃ Fin n) (h : ∀ v, η.hrv (π v) = π (θ.hrv v)) :
    η.hrvMonomial = θ.hrvMonomial := by
  unfold hrvMonomial
  rw [← Equiv.prod_comp π]
  apply Finset.prod_congr rfl
  intro r _
  simp only [θ.hrvFiber_card_conjugate η π h r]

end Orientation
end VerticalStripLLT.Circular
