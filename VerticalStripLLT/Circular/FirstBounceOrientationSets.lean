import VerticalStripLLT.Circular.FirstBounceOrientationSwap

set_option backward.isDefEq.respectTransparency false

/-! Edge sets, the target diagram, and sums over orientations. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- The HRV monomial of an edge set, or zero if it is not an orientation. -/
noncomputable def orientMono (A : Finset (Edge D.area)) : EExpansion :=
  if h : A ⊆ D.edgeData.normalEdges ∧ D.edgeData.Admissible A then
    Orientation.hrvMonomial (⟨A, h⟩ : Orientation D) else 0

theorem mem_normalEdges_iff (ε : Edge D.area) :
    ε ∈ D.edgeData.normalEdges ↔ ε ∉ D.strict := by
  simp [EdgeData.normalEdges, edgeData]

theorem orientMono_orientation (θ : Orientation D) : D.orientMono θ.val = θ.hrvMonomial := by
  unfold orientMono
  rw [dite_eq_left θ.property]
  rfl

theorem orientMono_of_not_adm {A : Finset (Edge D.area)} (h : ¬ D.edgeData.Admissible A) :
    D.orientMono A = 0 := by
  unfold orientMono
  rw [dite_eq_right (fun h' => h h'.2)]

theorem shiftedOrientationExpansion_eq_sum :
    shiftedOrientationExpansion D = ∑ A ∈ D.edgeData.normalEdges.powerset,
      MvPolynomial.C (Polynomial.X ^ A.card) * D.orientMono A := by
  unfold shiftedOrientationExpansion
  rw [← Finset.sum_filter_of_ne (p := fun A => D.edgeData.Admissible A)]
  · symm
    apply Finset.sum_bij (fun A hA => (⟨A, Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1,
      (Finset.mem_filter.mp hA).2⟩ : Orientation D))
    · intro _ _; exact Finset.mem_univ _
    · intro a _ b _ h
      exact congrArg Subtype.val h
    · intro θ _
      exact ⟨θ.val, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr θ.property.1,
        θ.property.2⟩, rfl⟩
    · intro A hA
      rw [orientMono, dite_eq_left]
  · intro A _ h
    by_contra hA
    exact h (by rw [D.orientMono_of_not_adm hA, mul_zero])

/-- Two orientation monomials agree if admissibility agrees and the monomials agree. -/
theorem orientMono_eq_of {D' : Diagram n} (A : Finset (Edge D.area))
    (A' : Finset (Edge D'.area)) (hA : A ⊆ D.edgeData.normalEdges)
    (hA' : A' ⊆ D'.edgeData.normalEdges)
    (h1 : ∀ h : D.edgeData.Admissible A, D'.edgeData.Admissible A' ∧
      ∀ h' : D'.edgeData.Admissible A',
        Orientation.hrvMonomial (⟨A', hA', h'⟩ : Orientation D') =
          Orientation.hrvMonomial (⟨A, hA, h⟩ : Orientation D))
    (h2 : D'.edgeData.Admissible A' → D.edgeData.Admissible A) :
    D.orientMono A = D'.orientMono A' := by
  by_cases h : D.edgeData.Admissible A
  · obtain ⟨h', hm⟩ := h1 h
    unfold orientMono
    rw [dite_eq_left ⟨hA, h⟩, dite_eq_left ⟨hA', h'⟩, hm h']
  · rw [D.orientMono_of_not_adm h, D'.orientMono_of_not_adm (fun h' => h (h2 h'))]

section NN

variable (e : Edge D.area) (he : e ∈ D.strict) (hlen : 2 ≤ e.length.val)
  (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)
  (hsame : D.boundary ((e.tail.val : ℤ) + 1) = D.boundary (e.tail.val : ℤ))
  (hleft : ¬ D.strictAt (e.tail.val : ℤ))
  (hright : ¬ D.strictAt ((e.tail.val : ℤ) + 1))

/-- The normal edges other than the shortened edge and the bridge. -/
noncomputable def baseSet : Finset (Edge D.area) :=
  ((D.edgeData.normalEdges).erase (D.shortenedOldEdge e he hlen)).erase (D.bridgeEdge e)

theorem mem_baseSet_iff (ε : Edge D.area) :
    ε ∈ D.baseSet e he hlen ↔ ε ∉ D.strict ∧ ε ≠ D.shortenedOldEdge e he hlen ∧
      ε ≠ D.bridgeEdge e := by
  simp only [baseSet, Finset.mem_erase, mem_normalEdges_iff]
  tauto

include hgap hsame hleft hright in
theorem nn_swapEdge_mem_baseSet (ε : Edge D.area) (hε : ε ∈ D.baseSet e he hlen) :
    D.swapEdge (e.tail.val : ℤ) ε ∈ D.baseSet e he hlen := by
  rw [mem_baseSet_iff] at hε ⊢
  obtain ⟨hs, hf, hb⟩ := hε
  have hinv := D.nn_swapEdge_swapEdge e he hlen hgap hsame ε hb
  have heb := D.nn_e_ne_bridge e he hsame hright
  refine ⟨?_, ?_, D.nn_swapEdge_ne_bridge e he hlen hgap hsame ε hb⟩
  · intro hs'
    by_cases hee : D.swapEdge (e.tail.val : ℤ) ε = e
    · apply hf
      rw [← hinv, hee, D.nn_swapEdge_e e he hlen hgap hsame hright]
    · have := D.nn_swapEdge_fix e he hlen hgap hsame hleft hright _ hs' hee
      rw [hinv] at this
      exact hs (this ▸ hs')
  · intro hf'
    apply hs
    rw [← hinv, hf', ← D.nn_swapEdge_e e he hlen hgap hsame hright,
      D.nn_swapEdge_swapEdge e he hlen hgap hsame e heb]
    exact he

/-- The swap acting on base edge sets. -/
noncomputable def swapSet (θ : Finset (Edge D.area)) : Finset (Edge D.area) :=
  θ.image (D.swapEdge (e.tail.val : ℤ))

include hgap hsame hleft hright in
theorem nn_swapSet_subset (θ : Finset (Edge D.area)) (hθ : θ ⊆ D.baseSet e he hlen) :
    D.swapSet e θ ⊆ D.baseSet e he hlen := by
  intro ε hε
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hε
  exact D.nn_swapEdge_mem_baseSet e he hlen hgap hsame hleft hright a (hθ ha)

include hgap hsame in
theorem nn_swapSet_swapSet (θ : Finset (Edge D.area)) (hθ : θ ⊆ D.baseSet e he hlen) :
    D.swapSet e (D.swapSet e θ) = θ := by
  unfold swapSet
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := θ)]
  apply Finset.image_congr
  intro a ha
  exact D.nn_swapEdge_swapEdge e he hlen hgap hsame a
    ((D.mem_baseSet_iff e he hlen a).mp (hθ ha)).2.2

include hgap hsame in
theorem nn_swapSet_card (θ : Finset (Edge D.area)) (hθ : θ ⊆ D.baseSet e he hlen) :
    (D.swapSet e θ).card = θ.card := by
  unfold swapSet
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have h1 := D.nn_swapEdge_swapEdge e he hlen hgap hsame a
    ((D.mem_baseSet_iff e he hlen a).mp (hθ ha)).2.2
  have h2 := D.nn_swapEdge_swapEdge e he hlen hgap hsame b
    ((D.mem_baseSet_iff e he hlen b).mp (hθ hb)).2.2
  rw [← h1, ← h2]
  exact congrArg _ hab

/-- Edge sets of the target diagram corresponding to edge sets of the source. -/
noncomputable def targetSet (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)
    (A : Finset (Edge D.area)) : Finset (Edge (D.shortenStrict e he hlen hgap).area) :=
  Finset.univ.filter fun b => D.cornerIncl e (D.strict_corner e he) b ∈ A

theorem mem_targetSet_iff (A : Finset (Edge D.area))
    (b : Edge (D.shortenStrict e he hlen hgap).area) :
    b ∈ D.targetSet e he hlen hgap A ↔ D.cornerIncl e (D.strict_corner e he) b ∈ A := by
  simp [targetSet]

theorem nn_liftStep_target (A : Finset (Edge D.area)) (hA : e ∉ A) (x y : ℤ) :
    (D.shortenStrict e he hlen hgap).liftStep (D.targetSet e he hlen hgap A) x y ↔
      ∃ ε ∈ insert (D.shortenedOldEdge e he hlen) (D.strict.erase e) ∪ A,
        D.residue x = ε.tail ∧ y = x + (ε.length.val : ℤ) := by
  constructor
  · rintro ⟨b, hb, hx, hy⟩
    refine ⟨D.cornerIncl e (D.strict_corner e he) b, ?_, hx, hy⟩
    rcases Finset.mem_union.mp hb with hb | hb
    · rcases (D.shortenStrict_strict_mem e he hlen hgap b).mp hb with hb | hb
      · subst hb
        exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨D.cornerIncl_ne _ _ _, hb⟩))
    · exact Finset.mem_union_right _ ((D.mem_targetSet_iff e he hlen hgap A b).mp hb)
  · rintro ⟨ε, hε, hx, hy⟩
    have hne : ε ≠ e := by
      intro hee
      rw [hee] at hε
      rcases Finset.mem_union.mp hε with h | h
      · rcases Finset.mem_insert.mp h with h | h
        · exact D.nn_fE_not_strict e he hlen (h ▸ he)
        · simp at h
      · exact hA h
    refine ⟨D.cornerRestrict e (D.strict_corner e he) ε hne, ?_, hx, hy⟩
    rcases Finset.mem_union.mp hε with h | h
    · apply Finset.mem_union_left
      rw [D.shortenStrict_strict_mem]
      rcases Finset.mem_insert.mp h with h | h
      · left
        apply D.cornerIncl_injective e (D.strict_corner e he)
        exact h
      · right
        exact (Finset.mem_erase.mp h).2
    · apply Finset.mem_union_right
      rw [D.mem_targetSet_iff]
      exact h

end NN

end Diagram

end VerticalStripLLT.Circular

