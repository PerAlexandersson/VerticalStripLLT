import VerticalStripLLT.OrientationFirstBounce
import VerticalStripLLT.SecondBounceGraph
-- Local helper module: VerticalStripLLT.SecondBounceRelations

/-! ## Upward relations of the second-bounce source and successor

The source `P = U d n V d e W` has normal edges `insert (y,t) N_B` and strict edges
`insert (a,i) (insert (i,t) S_B)`.  The successor `T = U n d V e d W` has normal edges
`insert (a,i) N_B` and strict edges `insert (a,y) (insert (y,t) S_B)`.  Orientations of
both are written as `Bool × Orientation B`, where the Boolean is the orientation of the
fresh normal edge `(y,t)` for `P`, respectively `(a,i)` for `T`. -/

namespace VerticalStripLLT
namespace BounceHRV

open scoped BigOperators

variable {n : ℕ}

/-- Upward steps of an orientation obtained by inserting one fresh normal edge, for an
arbitrary strict edge set of the enlarged path. -/
theorem upwardStep_insert_general {P R : SchroderPath n}
    (e : Fin n × Fin n) (hnot : e ∉ P.normalEdges)
    (hN : R.normalEdges = insert e P.normalEdges) (b : Bool) (θ : Orientation P)
    (u w : Fin n) :
    upwardStep R ((orientationInsertEquiv e hnot hN).symm (b, θ)) u w ↔
      (u, w) ∈ R.strictEdges ∨ (∃ h : (u, w) ∈ P.normalEdges, θ ⟨(u, w), h⟩ = true) ∨
        ((u, w) = e ∧ b = true) := by
  classical
  let E := orientationInsertEquiv e hnot hN
  let θR : Orientation R := E.symm (b, θ)
  change upwardStep R θR u w ↔ _
  have haR : e ∈ R.normalEdges := by
    rw [hN]; simp
  have oldR {f : Fin n × Fin n} (hf : f ∈ P.normalEdges) : f ∈ R.normalEdges := by
    rw [hN]; simp [hf]
  have hnew : θR ⟨e, haR⟩ = b := by
    simp [θR, E, orientationInsertEquiv]
  have hold {f : Fin n × Fin n} (hfP : f ∈ P.normalEdges) (hfR : f ∈ R.normalEdges) :
      θR ⟨f, hfR⟩ = θ ⟨f, hfP⟩ := by
    have hne : f ≠ e := by
      intro h; apply hnot; rw [← h]; exact hfP
    simp [θR, E, orientationInsertEquiv, hne]
  unfold upwardStep
  constructor
  · rintro (hs | ⟨hn, hv⟩)
    · exact Or.inl hs
    · have hn' := hn
      rw [hN, Finset.mem_insert] at hn'
      rcases hn' with he | hn'
      · refine Or.inr (Or.inr ⟨he, ?_⟩)
        have : (⟨(u, w), hn⟩ : {f // f ∈ R.normalEdges}) = ⟨e, haR⟩ := Subtype.ext he
        rw [this, hnew] at hv
        exact hv
      · exact Or.inr (Or.inl ⟨hn', by rw [← hold hn' hn]; exact hv⟩)
  · rintro (hs | ⟨hn, hv⟩ | ⟨he, hb⟩)
    · exact Or.inl hs
    · exact Or.inr ⟨oldR hn, by rw [hold hn (oldR hn)]; exact hv⟩
    · refine Or.inr ⟨by rw [he]; exact haR, ?_⟩
      have : (⟨(u, w), by rw [he]; exact haR⟩ : {f // f ∈ R.normalEdges}) =
        ⟨e, haR⟩ := Subtype.ext he
      rw [this, hnew, hb]

section SecondRelations

variable {B : SchroderPath n} {a i y t : Fin n}

/-- Upward steps of the second-bounce source orientation `(b, θ)`. -/
def RP2 (a i y t : Fin n) (b : Bool) (θ : Orientation B) (u w : Fin n) : Prop :=
  RP i y t b θ u w ∨ (u, w) = (a, i)

/-- Upward steps of the second-bounce successor orientation `(c, θ)`. -/
def RT2 (a i y t : Fin n) (c : Bool) (θ : Orientation B) (u w : Fin n) : Prop :=
  RT y t θ u w ∨ (u, w) = (a, y) ∨ ((u, w) = (a, i) ∧ c = true)

variable {P T : SchroderPath n}

theorem upwardStep_secondSource_iff (hfresh : (y, t) ∉ B.normalEdges)
    (hPN : P.normalEdges = insert (y, t) B.normalEdges)
    (hPS : P.strictEdges = insert (a, i) (insert (i, t) B.strictEdges))
    (b : Bool) (θ : Orientation B) (u w : Fin n) :
    upwardStep P ((orientationInsertEquiv (y, t) hfresh hPN).symm (b, θ)) u w ↔
      RP2 a i y t b θ u w := by
  rw [upwardStep_insert_general, hPS, Finset.mem_insert, Finset.mem_insert]
  unfold RP2 RP upwardStep
  tauto

theorem upwardStep_secondSucc_iff (hfresh : (a, i) ∉ B.normalEdges)
    (hTN : T.normalEdges = insert (a, i) B.normalEdges)
    (hTS : T.strictEdges = insert (a, y) (insert (y, t) B.strictEdges))
    (c : Bool) (θ : Orientation B) (u w : Fin n) :
    upwardStep T ((orientationInsertEquiv (a, i) hfresh hTN).symm (c, θ)) u w ↔
      RT2 a i y t c θ u w := by
  rw [upwardStep_insert_general, hTS, Finset.mem_insert, Finset.mem_insert]
  unfold RT2 RT upwardStep
  tauto

end SecondRelations

end BounceHRV
end VerticalStripLLT
