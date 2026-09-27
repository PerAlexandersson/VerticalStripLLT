import VerticalStripLLT.Components.GainContraction

/-!
# Weak connectivity under contraction

Contracting a subset of the selected edges preserves the spanning weak
components. This is independent of gains and of the potential used for
contraction, and includes isolated vertices, loops, and parallel edge instances.
-/

namespace VerticalStripLLT.Components.GainData

open scoped Classical

noncomputable section

variable {V E : Type*} [DecidableEq E] (G : GainData V E)

/-- Enlarging the selected edge set gives a map of spanning weak components. -/
def weakBlockMap {F X : Finset E} (hFX : F ⊆ X) : G.weakBlock F → G.weakBlock X :=
  Quotient.lift (G.weakBlockMk X) (fun x y hxy => by
    apply Quotient.sound
    apply Relation.EqvGen.mono (r := G.selectedRelation F) _ x y hxy
    rintro a b ⟨e, he, htail, hhead⟩
    exact ⟨e, hFX he, htail, hhead⟩)

@[simp]
theorem weakBlockMap_mk {F X : Finset E} (hFX : F ⊆ X) (v : V) :
    G.weakBlockMap hFX (G.weakBlockMk F v) = G.weakBlockMk X v := rfl

theorem weakBlockMap_surjective {F X : Finset E} (hFX : F ⊆ X) :
    Function.Surjective (G.weakBlockMap hFX) := by
  intro x
  obtain ⟨v, rfl⟩ := G.weakBlockMk_surjective X x
  exact ⟨G.weakBlockMk F v, rfl⟩

/-- Contracted connectivity identifies blocks with the same original component. -/
theorem weakBlockMap_eq_of_contraction_connected {F X : Finset E}
    (p : V → ℤ) (hFX : F ⊆ X) {a b : G.weakBlock F}
    (hab : Relation.EqvGen ((G.contraction F p).selectedRelation (X \ F)) a b) :
    G.weakBlockMap hFX a = G.weakBlockMap hFX b := by
  induction hab with
  | rel a b hab =>
    obtain ⟨e, he, rfl, rfl⟩ := hab
    change G.weakBlockMk X (G.tail e) = G.weakBlockMk X (G.head e)
    apply Quotient.sound
    exact Relation.EqvGen.rel _ _ ⟨e, (Finset.mem_sdiff.mp he).1, rfl, rfl⟩
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

/-- Contracting `F` and retaining precisely `X \ F` preserves weak connectivity. -/
theorem contraction_eqvGen_iff {F X : Finset E} (p : V → ℤ) (hFX : F ⊆ X)
    {x y : V} :
    Relation.EqvGen ((G.contraction F p).selectedRelation (X \ F))
      (G.weakBlockMk F x) (G.weakBlockMk F y) ↔
      Relation.EqvGen (G.selectedRelation X) x y := by
  constructor
  · intro h
    have hmap := G.weakBlockMap_eq_of_contraction_connected p hFX h
    exact G.weakBlockMk_eq_iff.mp hmap
  · intro h
    induction h with
    | rel x y hxy =>
      obtain ⟨e, he, rfl, rfl⟩ := hxy
      by_cases heF : e ∈ F
      · rw [G.weakBlockMk_tail_eq_head heF]
        exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ ⟨e, Finset.mem_sdiff.mpr ⟨he, heF⟩, rfl, rfl⟩
    | refl x => exact Relation.EqvGen.refl _
    | symm x y h ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z hxy hyz ihxy ihyz => exact Relation.EqvGen.trans _ _ _ ihxy ihyz

/-- The actual spanning weak-component quotients before and after contraction. -/
def contractionWeakBlockEquiv {F X : Finset E} (p : V → ℤ) (hFX : F ⊆ X) :
    (G.contraction F p).weakBlock (X \ F) ≃ G.weakBlock X where
  toFun := Quotient.lift (G.weakBlockMap hFX)
    (fun _ _ h => G.weakBlockMap_eq_of_contraction_connected p hFX h)
  invFun := Quotient.lift
    (fun v => (G.contraction F p).weakBlockMk (X \ F) (G.weakBlockMk F v))
    (fun _ _ h => Quotient.sound ((G.contraction_eqvGen_iff p hFX).mpr h))
  left_inv := by
    intro a
    refine Quotient.inductionOn a ?_
    intro b
    obtain ⟨v, rfl⟩ := G.weakBlockMk_surjective F b
    rfl
  right_inv := by
    intro a
    refine Quotient.inductionOn a ?_
    intro v
    rfl

@[simp]
theorem contractionWeakBlockEquiv_mk {F X : Finset E} (p : V → ℤ)
    (hFX : F ⊆ X) (v : V) :
    G.contractionWeakBlockEquiv p hFX
      ((G.contraction F p).weakBlockMk (X \ F) (G.weakBlockMk F v)) =
      G.weakBlockMk X v := rfl

/-- The weak-component count used in the coefficient sign survives contraction. -/
theorem contraction_weakComponentCount {F X : Finset E} (p : V → ℤ) (hFX : F ⊆ X) :
    OrderedPartitions.weakComponentCount
      ((G.contraction F p).selectedRelation (X \ F)) =
      OrderedPartitions.weakComponentCount (G.selectedRelation X) := by
  change Nat.card ((G.contraction F p).weakBlock (X \ F)) = Nat.card (G.weakBlock X)
  exact Nat.card_congr (G.contractionWeakBlockEquiv p hFX)

/-- Adding selected edges can only reduce the number of spanning weak components. -/
theorem weakComponentCount_le_of_subset [Fintype V] {F X : Finset E} (hFX : F ⊆ X) :
    OrderedPartitions.weakComponentCount (G.selectedRelation X) ≤
      OrderedPartitions.weakComponentCount (G.selectedRelation F) := by
  change Nat.card (G.weakBlock X) ≤ Nat.card (G.weakBlock F)
  exact Nat.card_le_card_of_surjective (G.weakBlockMap hFX)
    (G.weakBlockMap_surjective hFX)

end

end VerticalStripLLT.Components.GainData
