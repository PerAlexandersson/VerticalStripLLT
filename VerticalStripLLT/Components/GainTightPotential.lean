import VerticalStripLLT.Components.GainScaling
import VerticalStripLLT.Components.GainCoefficient

/-! Integer-scaled potentials which are tight on a balanced edge set. -/

namespace VerticalStripLLT.Components.GainData

open Classical

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq E] (G : GainData V E)

/-- A contracted-good pair admits a potential tight on `F` and strictly slack
on the remaining selected edges. -/
theorem exists_tightPotential_of_contractedGood
    (X F : Finset E) (_hFX : F ⊆ X) (hg : G.ContractedGood X F) :
    ∃ M : ℕ, 0 < M ∧ ∃ z : V → ℤ,
      (∀ e ∈ F, z (G.head e) - z (G.tail e) = (M : ℤ) * G.gain e) ∧
      (∀ e ∈ X \ F, (M : ℤ) * G.gain e <
        z (G.head e) - z (G.tail e)) := by
  obtain ⟨p, hp, hn, _ht⟩ := hg
  let M : ℕ := Fintype.card (G.weakBlock F) + 1
  have hM : Fintype.card (G.weakBlock F) ≤ M := by
    dsimp [M]
    lia
  have hMpos : 0 < M := by
    dsimp [M]
    lia
  obtain ⟨q, hq⟩ :=
    ((G.contraction F p).exists_feasible_strictScale_iff (X \ F) M hM).mpr hn
  let z : V → ℤ := fun v =>
    (M : ℤ) * p v + (q (G.weakBlockMk F v) : ℤ)
  refine ⟨M, hMpos, z, ?_, ?_⟩
  · intro e he
    have hblocks := G.weakBlockMk_tail_eq_head (F := F) he
    have hqblocks := congrArg q hblocks
    calc
      z (G.head e) - z (G.tail e) =
          (M : ℤ) * (p (G.head e) - p (G.tail e)) := by
            dsimp [z]
            rw [← hqblocks]
            ring
      _ = (M : ℤ) * G.gain e := by rw [hp e he]
  · intro e he
    have hfeas := hq e he
    change (q (G.weakBlockMk F (G.tail e)) : ℤ) +
        ((M : ℤ) * (G.gain e -
          (p (G.head e) - p (G.tail e))) + 1) ≤
      (q (G.weakBlockMk F (G.head e)) : ℤ) at hfeas
    dsimp [z]
    ring_nf at hfeas ⊢
    lia

end

end VerticalStripLLT.Components.GainData
