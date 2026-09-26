import VerticalStripLLT.Circular.FirstBounceOrientationSets

set_option backward.isDefEq.respectTransparency false

/-! Reindexing the target expansion by source edge sets. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

section NN

variable (e : Edge D.area) (he : e ∈ D.strict) (hlen : 2 ≤ e.length.val)
  (hgap : D.area.area (D.area.next e.head) < D.area.area e.head)
  (hsame : D.boundary ((e.tail.val : ℤ) + 1) = D.boundary (e.tail.val : ℤ))
  (hleft : ¬ D.strictAt (e.tail.val : ℤ))
  (hright : ¬ D.strictAt ((e.tail.val : ℤ) + 1))

/-- Inclusion of target edges. -/
noncomputable def inclEmb (hgap : D.area.area (D.area.next e.head) < D.area.area e.head) :
    Edge (D.shortenStrict e he hlen hgap).area ↪ Edge D.area :=
  ⟨D.cornerIncl e (D.strict_corner e he), D.cornerIncl_injective e (D.strict_corner e he)⟩

include hsame hright in
theorem nn_mem_targetNormal_iff (b : Edge (D.shortenStrict e he hlen hgap).area) :
    b ∈ (D.shortenStrict e he hlen hgap).edgeData.normalEdges ↔
      D.cornerIncl e (D.strict_corner e he) b ∈ insert (D.bridgeEdge e) (D.baseSet e he hlen) := by
  rw [mem_normalEdges_iff, D.shortenStrict_strict_mem, Finset.mem_insert, mem_baseSet_iff]
  have hb := D.nn_bridge_not_strict e hsame hright
  have hfb := D.nn_fE_ne_bridge e he hlen hsame
  have hiff : b = D.shortenedEdge e he hlen ↔
      D.cornerIncl e (D.strict_corner e he) b = D.shortenedOldEdge e he hlen :=
    ⟨fun h => h ▸ rfl, fun h => D.cornerIncl_injective e (D.strict_corner e he) h⟩
  rw [hiff]
  constructor
  · intro h
    push Not at h
    by_cases hbb : D.cornerIncl e (D.strict_corner e he) b = D.bridgeEdge e
    · exact Or.inl hbb
    · exact Or.inr ⟨h.2, h.1, hbb⟩
  · rintro (h | ⟨h1, h2, _⟩)
    · rw [h]
      rintro (h' | h')
      · exact hfb h'.symm
      · exact hb h'
    · rintro (h' | h')
      · exact h2 h'
      · exact h1 h'

theorem nn_ne_e_of_mem (A : Finset (Edge D.area))
    (hA : A ⊆ insert (D.bridgeEdge e) (D.baseSet e he hlen)) (hsame : D.boundary
      ((e.tail.val : ℤ) + 1) = D.boundary (e.tail.val : ℤ))
    (hright : ¬ D.strictAt ((e.tail.val : ℤ) + 1)) : e ∉ A := by
  intro h
  rcases Finset.mem_insert.mp (hA h) with h | h
  · exact D.nn_bridge_not_strict e hsame hright (h ▸ he)
  · exact ((D.mem_baseSet_iff e he hlen e).mp h).1 he

theorem nn_map_targetSet (A : Finset (Edge D.area)) (hA : e ∉ A) :
    (D.targetSet e he hlen hgap A).map (D.inclEmb e he hlen hgap) = A := by
  ext ε
  simp only [Finset.mem_map, mem_targetSet_iff]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro h
    have hne : ε ≠ e := fun h' => hA (h' ▸ h)
    exact ⟨D.cornerRestrict e (D.strict_corner e he) ε hne, h, rfl⟩

theorem nn_targetSet_map (B : Finset (Edge (D.shortenStrict e he hlen hgap).area)) :
    D.targetSet e he hlen hgap (B.map (D.inclEmb e he hlen hgap)) = B := by
  ext b
  rw [mem_targetSet_iff, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, hab⟩
    have : a = b := D.cornerIncl_injective e (D.strict_corner e he) hab
    exact this ▸ ha
  · intro hb
    exact ⟨b, hb, rfl⟩

theorem nn_card_targetSet (A : Finset (Edge D.area)) (hA : e ∉ A) :
    (D.targetSet e he hlen hgap A).card = A.card := by
  conv_rhs => rw [← D.nn_map_targetSet e he hlen hgap A hA]
  rw [Finset.card_map]

include hsame hright in
theorem nn_targetSet_subset (A : Finset (Edge D.area))
    (hA : A ⊆ insert (D.bridgeEdge e) (D.baseSet e he hlen)) :
    D.targetSet e he hlen hgap A ⊆ (D.shortenStrict e he hlen hgap).edgeData.normalEdges := by
  intro b hb
  rw [D.nn_mem_targetNormal_iff e he hlen hgap hsame hright]
  exact hA ((D.mem_targetSet_iff e he hlen hgap A b).mp hb)

include hsame hright in
theorem nn_target_sum :
    shiftedOrientationExpansion (D.shortenStrict e he hlen hgap) =
      ∑ A ∈ (insert (D.bridgeEdge e) (D.baseSet e he hlen)).powerset,
        MvPolynomial.C (Polynomial.X ^ A.card) *
          (D.shortenStrict e he hlen hgap).orientMono (D.targetSet e he hlen hgap A) := by
  rw [shiftedOrientationExpansion_eq_sum]
  apply Finset.sum_nbij' (fun B => B.map (D.inclEmb e he hlen hgap))
    (fun A => D.targetSet e he hlen hgap A)
  · intro B hB
    rw [Finset.mem_powerset] at hB ⊢
    intro ε hε
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hε
    exact (D.nn_mem_targetNormal_iff e he hlen hgap hsame hright b).mp (hB hb)
  · intro A hA
    rw [Finset.mem_powerset] at hA ⊢
    exact D.nn_targetSet_subset e he hlen hgap hsame hright A hA
  · intro B _
    exact D.nn_targetSet_map e he hlen hgap B
  · intro A hA
    rw [Finset.mem_powerset] at hA
    exact D.nn_map_targetSet e he hlen hgap A (D.nn_ne_e_of_mem e he hlen A hA hsame hright)
  · intro B _
    rw [D.nn_targetSet_map e he hlen hgap B, Finset.card_map]

end NN

end Diagram

end VerticalStripLLT.Circular

