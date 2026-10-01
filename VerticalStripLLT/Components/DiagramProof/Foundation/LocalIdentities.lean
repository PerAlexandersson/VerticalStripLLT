import VerticalStripLLT.Components.DiagramProof.Foundation.MarkedValues
import VerticalStripLLT.Components.DiagramProof.Foundation.PathTransport

/-! Marked local identities with arbitrary selected exterior. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical
open scoped BigOperators

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- Add one directed comparison to a selected relation. -/
def addPair (R : Fin n → Fin n → Prop) (a b u v : Fin n) : Prop :=
  R u v ∨ (u = a ∧ v = b)

theorem coloring_addPair_iff (R : Fin n → Fin n → Prop) (a b : Fin n)
    {m : ℕ} (c : Fin n → Fin m) :
    (∀ u v, addPair R a b u v → c u < c v) ↔
      (∀ u v, R u v → c u < c v) ∧ c a < c b := by
  constructor
  · intro hc
    exact ⟨fun u v h => hc u v (Or.inl h), hc a b (Or.inr ⟨rfl, rfl⟩)⟩
  · rintro ⟨hc, hab⟩ u v (h | ⟨rfl, rfl⟩)
    · exact hc u v h
    · exact hab

/-- The diamond is pointwise in colors, including the marked endpoint condition. -/
theorem markedRelationValue_diamond (R : Fin n → Fin n → Prop)
    (a b c v : Fin n) (hac : R a c) (m : ℕ) (β : Fin m) :
    markedRelationValue (addPair R a b) v m β +
        markedRelationValue (addPair R b c) v m β =
      markedRelationValue R v m β +
        markedRelationValue (addPair (addPair R a b) b c) v m β := by
  unfold markedRelationValue
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro κ _
  simp only [coloring_addPair_iff]
  by_cases hv : κ v = β
  · by_cases hR : ∀ u w, R u w → κ u < κ w
    · have hcover : κ a < κ b ∨ κ b < κ c := by
        by_cases hab : κ a < κ b
        · exact Or.inl hab
        · exact Or.inr ((le_of_not_gt hab).trans_lt (hR a c hac))
      rcases hcover with hab | hbc
      · by_cases hbc : κ b < κ c <;> simp [hv, hab, hbc]
      · by_cases hab : κ a < κ b <;> simp [hv, hab, hbc]
    · simp [hv, hR]
  · simp [hv]

/-- A comparison already forced by strict paths does not change marked K. -/
theorem markedRelationValue_eq_of_transGen_eq (R S : Fin n → Fin n → Prop)
    (hclosure : Relation.TransGen R = Relation.TransGen S)
    (v : Fin n) (m : ℕ) (β : Fin m) :
    markedRelationValue R v m β = markedRelationValue S v m β := by
  have extend {T : Fin n → Fin n → Prop} {κ : Fin n → Fin m}
      (hc : ∀ u w, T u w → κ u < κ w) {u w}
      (h : Relation.TransGen T u w) : κ u < κ w := by
    induction h with
    | single hs => exact hc _ _ hs
    | tail _ hs ih => exact ih.trans (hc _ _ hs)
  unfold markedRelationValue
  apply Finset.sum_congr rfl
  intro κ _
  have hiff : (∀ u w, R u w → κ u < κ w) ↔ (∀ u w, S u w → κ u < κ w) := by
    constructor
    · intro hc u w hs
      apply extend hc
      rw [hclosure]
      exact Relation.TransGen.single hs
    · intro hc u w hr
      apply extend hc
      rw [← hclosure]
      exact Relation.TransGen.single hr
  exact ite_congr (propext (and_congr_right fun _ => hiff)) (fun _ => rfl) (fun _ => rfl)

/-- A map decreasing on selected steps decreases along their paths. -/
theorem antitone_on_reachable {V W : Type*} [Preorder W] {R : V → V → Prop}
    (H : V → W) (hstep : ∀ u v, R u v → H v ≤ H u) {u v : V}
    (h : Relation.ReflTransGen R u v) : H v ≤ H u := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact (hstep _ _ hs).trans ih

/-- An upper bound supplied by another forward HRV map bounds the actual HRV. -/
theorem hrv_le_of_selected_hrv_le (hforward : Forward D) (θ η : Orientation D)
    (hstep : ∀ u v, D.edgeData.selected θ.val u v → η.hrv v ≤ η.hrv u)
    (u : Fin n) : θ.hrv u ≤ η.hrv u := by
  exact (η.reachable_le_hrv_of_forward hforward Relation.ReflTransGen.refl).trans
    (antitone_on_reachable η.hrv hstep (θ.hrv_reachable u))

theorem hrv_le_of_selected_subset (hforward : Forward D) (θ η : Orientation D)
    (hsub : ∀ u v, D.edgeData.selected θ.val u v → D.edgeData.selected η.val u v)
    (u : Fin n) : θ.hrv u ≤ η.hrv u :=
  hrv_le_of_selected_hrv_le hforward θ η
    (fun u v h => η.hrv_le_of_reachable_forward hforward
      (Relation.ReflTransGen.single (hsub u v h))) u

/-- Adding an edge whose head has no larger HRV preserves the entire HRV map. -/
theorem hrv_eq_of_addPair (hforward : Forward D) (θ η : Orientation D) (a b : Fin n)
    (hrel : ∀ u v, D.edgeData.selected θ.val u v ↔
      addPair (D.edgeData.selected η.val) a b u v)
    (hle : η.hrv b ≤ η.hrv a) : θ.hrv = η.hrv := by
  funext u
  apply le_antisymm
  · apply hrv_le_of_selected_hrv_le hforward θ η
    intro x y hs
    rcases (hrel x y).mp hs with hs | ⟨rfl, rfl⟩
    · exact η.hrv_le_of_reachable_forward hforward (Relation.ReflTransGen.single hs)
    · exact hle
  · exact hrv_le_of_selected_subset hforward η θ
      (fun x y hs => (hrel x y).mpr (Or.inl hs)) u

/-- A single added edge gives a uniform bound by the old HRVs of source and new head. -/
theorem hrv_addPair_le_max (hforward : Forward D) (θ η : Orientation D) (a b : Fin n)
    (hrel : ∀ u v, D.edgeData.selected θ.val u v ↔
      addPair (D.edgeData.selected η.val) a b u v) (u : Fin n) :
    θ.hrv u ≤ max (η.hrv u) (η.hrv b) := by
  have bound {v : Fin n} (hp : Relation.ReflTransGen (D.edgeData.selected θ.val) u v) :
      η.hrv v ≤ max (η.hrv u) (η.hrv b) := by
    induction hp with
    | refl => exact le_max_left _ _
    | @tail v w _ hs ih =>
      rcases (hrel v w).mp hs with hs | ⟨rfl, rfl⟩
      · exact (η.hrv_le_of_reachable_forward hforward
          (Relation.ReflTransGen.single hs)).trans ih
      · exact le_max_right _ _
  exact (η.reachable_le_hrv_of_forward hforward Relation.ReflTransGen.refl).trans
    (bound (θ.hrv_reachable u))

/-- A diamond preserves the unordered pair of entire HRV maps, with arbitrary exterior. -/
theorem diamond_hrv_maps (hforward : Forward D) (θ₀ θab θbc θabc : Orientation D)
    (a b c : Fin n) (hac : D.edgeData.selected θ₀.val a c)
    (hab : ∀ u v, D.edgeData.selected θab.val u v ↔
      addPair (D.edgeData.selected θ₀.val) a b u v)
    (hbc : ∀ u v, D.edgeData.selected θbc.val u v ↔
      addPair (D.edgeData.selected θ₀.val) b c u v)
    (habc : ∀ u v, D.edgeData.selected θabc.val u v ↔
      addPair (D.edgeData.selected θab.val) b c u v) :
    (θab.hrv = θ₀.hrv ∧ θbc.hrv = θabc.hrv) ∨
      (θab.hrv = θabc.hrv ∧ θbc.hrv = θ₀.hrv) := by
  have hacH : θ₀.hrv c ≤ θ₀.hrv a :=
    θ₀.hrv_le_of_reachable_forward hforward (Relation.ReflTransGen.single hac)
  have habc' : ∀ u v, D.edgeData.selected θabc.val u v ↔
      addPair (D.edgeData.selected θbc.val) a b u v := by
    intro u v
    simp only [habc, addPair, hab, hbc]
    tauto
  by_cases h : θ₀.hrv b ≤ θ₀.hrv c
  · refine Or.inl ⟨hrv_eq_of_addPair hforward θab θ₀ a b hab (h.trans hacH), ?_⟩
    apply Eq.symm
    apply hrv_eq_of_addPair hforward θabc θbc a b habc'
    have hupper := hrv_addPair_le_max hforward θbc θ₀ b c hbc b
    rw [max_eq_right h] at hupper
    exact hupper.trans (hacH.trans (hrv_le_of_selected_subset hforward θ₀ θbc
      (fun u v hs => (hbc u v).mpr (Or.inl hs)) a))
  · have h' := le_of_not_ge h
    refine Or.inr ⟨?_, hrv_eq_of_addPair hforward θbc θ₀ b c hbc h'⟩
    apply Eq.symm
    apply hrv_eq_of_addPair hforward θabc θab b c habc
    have hupper := hrv_addPair_le_max hforward θab θ₀ a b hab c
    rw [max_eq_right h'] at hupper
    exact hupper.trans (hrv_le_of_selected_subset hforward θ₀ θab
      (fun u v hs => (hab u v).mpr (Or.inl hs)) b)

theorem markedK_diamond (θ₀ θab θbc θabc : Orientation D)
    (a b c v : Fin n) (hac : D.edgeData.selected θ₀.val a c)
    (hab : ∀ u w, D.edgeData.selected θab.val u w ↔
      addPair (D.edgeData.selected θ₀.val) a b u w)
    (hbc : ∀ u w, D.edgeData.selected θbc.val u w ↔
      addPair (D.edgeData.selected θ₀.val) b c u w)
    (habc : ∀ u w, D.edgeData.selected θabc.val u w ↔
      addPair (D.edgeData.selected θab.val) b c u w) (m : ℕ) (β : Fin m) :
    markedK θab v m β + markedK θbc v m β = markedK θ₀ v m β + markedK θabc v m β := by
  unfold markedK
  rw [funext fun u => funext fun w => propext (habc u w),
    funext fun u => funext fun w => propext (hab u w),
    funext fun u => funext fun w => propext (hbc u w)]
  exact markedRelationValue_diamond _ a b c v hac m β

theorem markedE_diamond (hforward : Forward D) (θ₀ θab θbc θabc : Orientation D)
    (a b c v : Fin n) (hac : D.edgeData.selected θ₀.val a c)
    (hab : ∀ u w, D.edgeData.selected θab.val u w ↔
      addPair (D.edgeData.selected θ₀.val) a b u w)
    (hbc : ∀ u w, D.edgeData.selected θbc.val u w ↔
      addPair (D.edgeData.selected θ₀.val) b c u w)
    (habc : ∀ u w, D.edgeData.selected θabc.val u w ↔
      addPair (D.edgeData.selected θab.val) b c u w) (m : ℕ) (β : Fin m) :
    markedE θab v m β + markedE θbc v m β = markedE θ₀ v m β + markedE θabc v m β := by
  rcases diamond_hrv_maps hforward θ₀ θab θbc θabc a b c hac hab hbc habc with
    ⟨habH, hbcH⟩ | ⟨habH, hbcH⟩
  · simp only [markedE, habH, hbcH]
  · simpa only [markedE, habH, hbcH] using
      add_comm (markedE θabc v m β) (markedE θ₀ v m β)

/-- Closure-preserving changes preserve the entire forward HRV map. -/
theorem hrv_eq_of_reachable_eq {E : Diagram n} (hD : Forward D) (hE : Forward E)
    (θ : Orientation D) (η : Orientation E)
    (hclosure : Relation.ReflTransGen (D.edgeData.selected θ.val) =
      Relation.ReflTransGen (E.edgeData.selected η.val)) : θ.hrv = η.hrv := by
  funext u
  apply le_antisymm
  · apply η.reachable_le_hrv_of_forward hE
    rw [← hclosure]
    exact θ.hrv_reachable u
  · apply θ.reachable_le_hrv_of_forward hD
    rw [hclosure]
    exact η.hrv_reachable u

theorem markedK_eq_of_transGen_eq {E : Diagram n} (θ : Orientation D) (η : Orientation E)
    (hclosure : Relation.TransGen (D.edgeData.selected θ.val) =
      Relation.TransGen (E.edgeData.selected η.val)) (v : Fin n) (m : ℕ) (β : Fin m) :
    markedK θ v m β = markedK η v m β :=
  markedRelationValue_eq_of_transGen_eq _ _ hclosure v m β

theorem markedE_eq_of_reachable_eq {E : Diagram n} (hD : Forward D) (hE : Forward E)
    (θ : Orientation D) (η : Orientation E)
    (hclosure : Relation.ReflTransGen (D.edgeData.selected θ.val) =
      Relation.ReflTransGen (E.edgeData.selected η.val)) (v : Fin n) (m : ℕ) (β : Fin m) :
    markedE θ v m β = markedE η v m β := by
  unfold markedE
  rw [hrv_eq_of_reachable_eq hD hE θ η hclosure]

theorem markedValues_eq_of_transGen_eq {E : Diagram n} (hD : Forward D) (hE : Forward E)
    (θ : Orientation D) (η : Orientation E)
    (hclosure : Relation.TransGen (D.edgeData.selected θ.val) =
      Relation.TransGen (E.edgeData.selected η.val)) (v : Fin n) (m : ℕ) (β : Fin m) :
    markedK θ v m β = markedK η v m β ∧ markedE θ v m β = markedE η v m β := by
  refine ⟨markedK_eq_of_transGen_eq θ η hclosure v m β, ?_⟩
  apply markedE_eq_of_reachable_eq hD hE θ η ?_ v m β
  funext u w
  apply propext
  simp only [Relation.reflTransGen_iff_eq_or_transGen, hclosure]

/-- Reindex actual colors, carrying the marked endpoint along the vertex bijection. -/
theorem markedRelationValue_relabel (R S : Fin n → Fin n → Prop) (σ : Fin n ≃ Fin n)
    (hrel : ∀ u w, S u w ↔ R (σ u) (σ w)) (v : Fin n) (m : ℕ) (β : Fin m) :
    markedRelationValue S v m β = markedRelationValue R (σ v) m β := by
  let colors : (Fin n → Fin m) ≃ (Fin n → Fin m) := {
    toFun := fun κ => κ ∘ σ.symm
    invFun := fun κ => κ ∘ σ
    left_inv := by intro κ; funext u; simp
    right_inv := by intro κ; funext u; simp
  }
  unfold markedRelationValue
  apply Fintype.sum_equiv colors
  intro κ
  have hadm : (∀ u w, S u w → κ u < κ w) ↔
      (∀ u w, R u w → (κ ∘ σ.symm) u < (κ ∘ σ.symm) w) := by
    constructor
    · intro hc u w h
      apply hc
      apply (hrel _ _).mpr
      simpa only [Equiv.apply_symm_apply] using h
    · intro hc u w h
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hc _ _ ((hrel u w).mp h)
  have hmark : κ v = β ↔ (κ ∘ σ.symm) (σ v) = β := by simp
  have hprod : EdgeData.monomial κ = EdgeData.monomial (κ ∘ σ.symm) := by
    exact (Equiv.prod_comp σ.symm (fun u => (MvPolynomial.X (κ u) : XPoly m))).symm
  exact ite_congr (propext (and_congr hmark hadm)) (fun _ => hprod) (fun _ => rfl)

end

end VerticalStripLLT.Circular.DiagramProof
