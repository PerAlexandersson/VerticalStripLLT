import VerticalStripLLT.BounceOrientationOps
-- Local helper module: VerticalStripLLT.BounceRelations

/-! ## Upward relations of the source, successor and background orientations -/

namespace VerticalStripLLT
namespace BounceHRV

open scoped BigOperators

variable {n : ℕ}

section Relations

variable {B : SchroderPath n} {i y : Fin n}

/-- Upward steps of the background, with the edge `(i,y)` removed. -/
def r0 (i y : Fin n) (θ : Orientation B) (u w : Fin n) : Prop :=
  upwardStep B θ u w ∧ (u, w) ≠ (i, y)

theorem r0_lt {θ : Orientation B} {u w : Fin n} (h : r0 i y θ u w) : u < w :=
  upwardStep_lt h.1

theorem r0_setBit (β : Bool) (θ : Orientation B) (u w : Fin n) :
    r0 i y (setBit i y β θ) u w ↔ r0 i y θ u w := by
  unfold r0 upwardStep
  by_cases h : (u, w) = (i, y)
  · simp [h]
  · simp [h, setBit]

theorem upwardStep_iff_r0 (hiy : (i, y) ∈ B.normalEdges) (θ : Orientation B) (u w : Fin n) :
    upwardStep B θ u w ↔ r0 i y θ u w ∨ ((u, w) = (i, y) ∧ bitOf hiy θ = true) := by
  unfold r0
  by_cases h : (u, w) = (i, y)
  · simp only [h, ne_eq, not_true_eq_false, and_false, true_and, false_or]
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have hns : (u, w) ∉ B.strictEdges := fun hs =>
      Finset.disjoint_left.1 B.normalEdges_disjoint_strictEdges hiy hs
    unfold upwardStep bitOf
    simp [hns, hiy]
  · simp [h]

theorem strict_swap_iff (hSinv : B.strictEdges.map (swapVertexPair i y) = B.strictEdges)
    (u w : Fin n) :
    (u, w) ∈ B.strictEdges ↔ (Equiv.swap i y u, Equiv.swap i y w) ∈ B.strictEdges := by
  constructor
  · intro h
    simpa [swapVertexPair_apply] using mem_of_map_swapVertexPair_eq i y hSinv h
  · intro h
    simpa [swapVertexPair_apply] using mem_of_map_swapVertexPair_eq i y hSinv h

theorem normal_swap_iff (hNinv : (B.normalEdges.erase (i, y)).map (swapVertexPair i y) =
    B.normalEdges.erase (i, y)) {u w : Fin n} (h1 : (u, w) ≠ (i, y))
    (h2 : (Equiv.swap i y u, Equiv.swap i y w) ≠ (i, y)) :
    (u, w) ∈ B.normalEdges ↔ (Equiv.swap i y u, Equiv.swap i y w) ∈ B.normalEdges := by
  constructor
  · intro h
    have := mem_of_map_swapVertexPair_eq i y hNinv (Finset.mem_erase.2 ⟨h1, h⟩)
    simpa [swapVertexPair_apply] using (Finset.mem_erase.1 this).2
  · intro h
    have := mem_of_map_swapVertexPair_eq i y hNinv (Finset.mem_erase.2 ⟨h2, h⟩)
    simpa [swapVertexPair_apply] using (Finset.mem_erase.1 this).2

theorem r0_swapO (hy : y.val = i.val + 1)
    (hSinv : B.strictEdges.map (swapVertexPair i y) = B.strictEdges)
    (hNinv : (B.normalEdges.erase (i, y)).map (swapVertexPair i y) =
      B.normalEdges.erase (i, y)) (θ : Orientation B) (u w : Fin n) :
    r0 i y (swapO hNinv θ) u w ↔ r0 i y θ (Equiv.swap i y u) (Equiv.swap i y w) := by
  have hiy : i ≠ y := by
    intro h; rw [h] at hy; lia
  by_cases h1 : (u, w) = (i, y)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    simp only [r0, ne_eq, not_true_eq_false, and_false, false_iff, Equiv.swap_apply_left,
      Equiv.swap_apply_right, not_and]
    intro h
    have := upwardStep_lt h
    rw [Fin.lt_def] at this
    lia
  by_cases h2 : (u, w) = (y, i)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    simp only [r0, Equiv.swap_apply_left, Equiv.swap_apply_right, ne_eq,
      not_true_eq_false, and_false, iff_false, not_and]
    intro h
    have := upwardStep_lt h
    rw [Fin.lt_def] at this
    lia
  have h3 : (Equiv.swap i y u, Equiv.swap i y w) ≠ (i, y) := by
    intro h
    apply h2
    have e1 := congrArg (fun p => Equiv.swap i y p.1) h
    have e2 := congrArg (fun p => Equiv.swap i y p.2) h
    simp only [Equiv.swap_apply_self, Equiv.swap_apply_left, Equiv.swap_apply_right] at e1 e2
    rw [e1, e2]
  simp only [r0, ne_eq, h1, h3, not_false_eq_true, and_true]
  unfold upwardStep
  rw [strict_swap_iff hSinv u w]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨hn, hv⟩
    refine ⟨(normal_swap_iff hNinv h1 h3).1 hn, ?_⟩
    rw [swapO_apply_of_ne hNinv θ hn h1] at hv
    exact hv
  · rintro ⟨hn, hv⟩
    refine ⟨(normal_swap_iff hNinv h1 h3).2 hn, ?_⟩
    rw [swapO_apply_of_ne hNinv θ _ h1]
    exact hv

variable (t : Fin n)

/-- Upward steps of the source orientation `(b, θ)`. -/
def RP (i y t : Fin n) (b : Bool) (θ : Orientation B) (u w : Fin n) : Prop :=
  upwardStep B θ u w ∨ (u, w) = (i, t) ∨ ((u, w) = (y, t) ∧ b = true)

/-- Upward steps of the successor orientation `θ`. -/
def RT (y t : Fin n) (θ : Orientation B) (u w : Fin n) : Prop :=
  upwardStep B θ u w ∨ (u, w) = (y, t)

variable {P T : SchroderPath n}

theorem upwardStep_source_iff (hfresh : (y, t) ∉ B.normalEdges)
    (hPN : P.normalEdges = insert (y, t) B.normalEdges)
    (hPS : P.strictEdges = insert (i, t) B.strictEdges) (b : Bool) (θ : Orientation B)
    (u w : Fin n) :
    upwardStep P ((orientationInsertEquiv (y, t) hfresh hPN).symm (b, θ)) u w ↔
      RP i y t b θ u w := by
  classical
  let E := orientationInsertEquiv (y, t) hfresh hPN
  let θR : Orientation P := E.symm (b, θ)
  change upwardStep P θR u w ↔ _
  have haR : (y, t) ∈ P.normalEdges := by
    rw [hPN]; simp
  have oldR {e : Fin n × Fin n} (he : e ∈ B.normalEdges) : e ∈ P.normalEdges := by
    rw [hPN]; simp [he]
  have hnew : θR ⟨(y, t), haR⟩ = b := by
    simp [θR, E, orientationInsertEquiv]
  have hold {e : Fin n × Fin n} (heB : e ∈ B.normalEdges) (heP : e ∈ P.normalEdges) :
      θR ⟨e, heP⟩ = θ ⟨e, heB⟩ := by
    have hne : e ≠ (y, t) := by
      intro h; apply hfresh; rw [← h]; exact heB
    simp [θR, E, orientationInsertEquiv, hne]
  unfold RP upwardStep
  rw [hPS, Finset.mem_insert]
  constructor
  · rintro ((hs | hs) | ⟨hn, hv⟩)
    · exact Or.inr (Or.inl hs)
    · exact Or.inl (Or.inl hs)
    · have hn' := hn
      rw [hPN, Finset.mem_insert] at hn'
      rcases hn' with he | hn'
      · refine Or.inr (Or.inr ⟨he, ?_⟩)
        have : (⟨(u, w), hn⟩ : {e // e ∈ P.normalEdges}) = ⟨(y, t), haR⟩ := Subtype.ext he
        rw [this, hnew] at hv
        exact hv
      · exact Or.inl (Or.inr ⟨hn', by rw [← hold hn' hn]; exact hv⟩)
  · rintro ((hs | ⟨hn, hv⟩) | hs | ⟨he, hb⟩)
    · exact Or.inl (Or.inr hs)
    · exact Or.inr ⟨oldR hn, by rw [hold hn (oldR hn)]; exact hv⟩
    · exact Or.inl (Or.inl hs)
    · refine Or.inr ⟨by rw [he]; exact haR, ?_⟩
      have : (⟨(u, w), by rw [he]; exact haR⟩ : {e // e ∈ P.normalEdges}) =
        ⟨(y, t), haR⟩ := Subtype.ext he
      rw [this, hnew, hb]

theorem upwardStep_succ_iff (hTN : B.normalEdges = T.normalEdges)
    (hTS : T.strictEdges = insert (y, t) B.strictEdges) (θ : Orientation B) (u w : Fin n) :
    upwardStep T (orientationTransport hTN θ) u w ↔ RT y t θ u w := by
  rw [upwardStep_transport_iff, hTS, Finset.mem_insert]
  unfold RT upwardStep
  tauto

end Relations

end BounceHRV
end VerticalStripLLT
