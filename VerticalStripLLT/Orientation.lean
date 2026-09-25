import VerticalStripLLT.PathInvariants

namespace VerticalStripLLT

abbrev Orientation {n : ℕ} (P : SchroderPath n) :=
  {e // e ∈ P.normalEdges} → Bool

def orientationAsc {n : ℕ} (P : SchroderPath n) (θ : Orientation P) : ℕ :=
  (Finset.univ.filter fun e => θ e = true).card

def upwardStep {n : ℕ} (P : SchroderPath n) (θ : Orientation P)
    (u v : Fin n) : Prop :=
  (u, v) ∈ P.strictEdges ∨
    ∃ h : (u, v) ∈ P.normalEdges, θ ⟨(u, v), h⟩ = true

theorem upwardStep_lt {n : ℕ} {P : SchroderPath n} {θ : Orientation P}
    {u v : Fin n} (h : upwardStep P θ u v) : u < v := by
  rcases h with hs | ⟨hn, _⟩
  · change u.val < v.val
    exact P.strictEdges_lt hs
  · change u.val < v.val
    exact P.normalEdges_lt hn

end VerticalStripLLT
