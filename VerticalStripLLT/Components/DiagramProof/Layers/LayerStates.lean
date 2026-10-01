import VerticalStripLLT.Components.DiagramProof.Corrections.AlternatingCertificate

/-!
# States of a forward diagram as sets of normal pairs

Every subset of the normal natural pairs, together with all strict pairs, is the
selected relation of exactly one state of a forward diagram. Summing over an
edge layer of fixed total selected size is therefore summing over the subsets of
normal pairs of one fixed size.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n} (hD : Forward D)

/-- The natural pairs which are not strict. -/
def normalPairs (D : Diagram n) : Finset (Fin n × Fin n) := naturalPairs D \ strictPairs D

@[simp]
theorem mem_normalPairs {x : Fin n × Fin n} :
    x ∈ normalPairs D ↔ naturalRel D x.1 x.2 ∧ ¬ strictRel D x.1 x.2 := by
  simp [normalPairs]

/-- The state selecting the strict pairs and the natural pairs in `T`. -/
def stateOf (T : Finset (Fin n × Fin n)) : Orientation D :=
  ofSelectedRelation hD (fun u v => strictRel D u v ∨ ((u, v) ∈ T ∧ naturalRel D u v))
    (by
      rintro u v (h | h)
      · exact naturalRel_of_strictRel h
      · exact h.2)
    (fun e he => Or.inl ⟨e, he, rfl, rfl⟩)

@[simp]
theorem stateOf_selected (T : Finset (Fin n × Fin n)) (u v : Fin n) :
    D.edgeData.selected (stateOf hD T).val u v ↔
      strictRel D u v ∨ ((u, v) ∈ T ∧ naturalRel D u v) :=
  selected_ofSelectedRelation ..

/-- The selected normal pairs of a state. -/
def normalSel (θ : Orientation D) : Finset (Fin n × Fin n) :=
  (normalPairs D).filter fun x => D.edgeData.selected θ.val x.1 x.2

theorem normalSel_subset (θ : Orientation D) : normalSel θ ⊆ normalPairs D :=
  Finset.filter_subset _ _

theorem stateOf_normalSel (θ : Orientation D) : stateOf hD (normalSel θ) = θ := by
  apply orientation_eq_of_selected_iff
  intro u v
  rw [stateOf_selected]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact selected_of_strictRel θ h
    · exact (Finset.mem_filter.mp h).2
  · intro h
    by_cases hs : strictRel D u v
    · exact Or.inl hs
    · exact Or.inr ⟨Finset.mem_filter.mpr ⟨mem_normalPairs.mpr
        ⟨naturalRel_of_selected h, hs⟩, h⟩, naturalRel_of_selected h⟩

theorem normalSel_stateOf {T : Finset (Fin n × Fin n)} (hT : T ⊆ normalPairs D) :
    normalSel (stateOf hD T) = T := by
  ext x
  simp only [normalSel, Finset.mem_filter, stateOf_selected]
  constructor
  · rintro ⟨hx, h | ⟨h, -⟩⟩
    · exact ((mem_normalPairs.mp hx).2 h).elim
    · exact h
  · intro h
    have hx := mem_normalPairs.mp (hT h)
    exact ⟨hT h, Or.inr ⟨h, hx.1⟩⟩

theorem totalSelected_stateOf {T : Finset (Fin n × Fin n)} (hT : T ⊆ normalPairs D) :
    totalSelected (stateOf hD T) = (strictPairs D).card + T.card := by
  rw [totalSelected_eq_card_selected, ← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, stateOf_selected,
      Finset.mem_union, mem_strictPairs]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨h, (mem_normalPairs.mp (hT h)).1⟩
  · rw [Finset.disjoint_left]
    intro x hs hT'
    exact (mem_normalPairs.mp (hT hT')).2 (mem_strictPairs.mp hs)

/-- Layer sums are sums over normal subsets of the corresponding size. -/
theorem sum_edgeLayer_eq {M : Type*} [AddCommMonoid M] (s : ℕ) (f : Orientation D → M) :
    ∑ θ ∈ edgeLayer D s, f θ = ∑ T ∈ (normalPairs D).powerset,
      if (strictPairs D).card + T.card = s then f (stateOf hD T) else 0 := by
  rw [edgeLayer, Finset.sum_filter]
  apply Finset.sum_nbij' normalSel (stateOf hD)
  · intro θ _
    exact Finset.mem_powerset.mpr (normalSel_subset θ)
  · intro T _
    exact Finset.mem_univ _
  · intro θ _
    exact stateOf_normalSel hD θ
  · intro T hT
    exact normalSel_stateOf hD (Finset.mem_powerset.mp hT)
  · intro θ _
    rw [stateOf_normalSel hD θ, ← totalSelected_stateOf hD (normalSel_subset θ),
      stateOf_normalSel hD θ]

/-- The right-marked strict-coloring value of an entire edge layer. -/
def layerK (D : Diagram n) (v : Fin n) (s : ℕ) (m : ℕ) (β : Fin m) : XPoly m :=
  ∑ θ ∈ edgeLayer D s, markedK θ v m β

/-- The right-marked HRV value of an entire edge layer. -/
def layerE (D : Diagram n) (v : Fin n) (s : ℕ) (m : ℕ) (β : Fin m) : XPoly m :=
  ∑ θ ∈ edgeLayer D s, markedE θ v m β

theorem edgeLayer_closed (s : ℕ) :
    ∀ θ ∈ edgeLayer D s, flipComponent D θ ⊆ edgeLayer D s :=
  fun _ hθ => flipComponent_subset_edgeLayer hθ

end

end VerticalStripLLT.Circular.DiagramProof
