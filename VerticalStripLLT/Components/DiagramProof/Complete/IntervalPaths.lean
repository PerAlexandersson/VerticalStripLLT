import VerticalStripLLT.Components.DiagramProof.Complete.Opening
import VerticalStripLLT.Components.DiagramProof.Complete.ChainConnected

/-! Open a chain, lift a smaller interval path, then close with the exterior restored. -/

namespace VerticalStripLLT.Circular.DiagramProof

/-- The opened restriction satisfies the smaller connected active-layer hypotheses. -/
theorem openCompleteChain_interval_connected_cover {n a m : ℕ}
    (ha : 0 < a) (hb : a + m ≤ n) (θ : Orientation (completeDiagram n))
    (hrow : ∀ v, (completeDiagram n).edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hchain : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected θ.val u v) :
    let α := completeRestrictAlong (intervalEmbed a m ha hb)
      (openCompleteChain θ (intervalEmbed a m ha hb (Fin.last (m + 1)))
        (intervalEmbed_last_pos ha hb))
    SelectedConnected α ∧ Cover α 0 (Fin.last (m + 1)) :=
  selectedConnected_and_cover_of_selected_chain (complete_forward (m + 1)) _
    (Nat.succ_pos m) (openCompleteChain_interval_row ha hb θ hrow)
    (openCompleteChain_interval_chain ha hb θ hchain)

/-- Two chain states differing only inside the interval connect whenever their
opened restrictions connect. All exterior edges are restored at the endpoint. -/
theorem complete_interval_chain_path_of_chain_above {n a m : ℕ} (ha : 0 < a) (hb : a + m ≤ n)
    (θ η : Orientation (completeDiagram n))
    (hrowθ : ∀ v, (completeDiagram n).edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hrowη : ∀ v, (completeDiagram n).edgeData.selected η.val 0 v ↔ v = Fin.last n)
    (hchainθ : ∀ u v : Fin (n + 1),
      intervalEmbed a m ha hb (Fin.last (m + 1)) ≤ u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected θ.val u v)
    (hchainη : ∀ u v : Fin (n + 1),
      intervalEmbed a m ha hb (Fin.last (m + 1)) ≤ u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected η.val u v)
    (houtside : ∀ u v, (¬ ∃ i j,
      intervalEmbed a m ha hb i = u ∧ intervalEmbed a m ha hb j = v) →
      ((completeDiagram n).edgeData.selected θ.val u v ↔
        (completeDiagram n).edgeData.selected η.val u v))
    (hpath : Relation.ReflTransGen (Flip (completeDiagram (m + 1)))
      (completeRestrictAlong (intervalEmbed a m ha hb)
        (openCompleteChain θ (intervalEmbed a m ha hb (Fin.last (m + 1)))
          (intervalEmbed_last_pos ha hb)))
      (completeRestrictAlong (intervalEmbed a m ha hb)
        (openCompleteChain η (intervalEmbed a m ha hb (Fin.last (m + 1)))
          (intervalEmbed_last_pos ha hb)))) :
    Relation.ReflTransGen (Flip (completeDiagram n)) θ η := by
  let ι := intervalEmbed a m ha hb
  let b := ι (Fin.last (m + 1))
  let β := openCompleteChain θ b (intervalEmbed_last_pos ha hb)
  let γ := openCompleteChain η b (intervalEmbed_last_pos ha hb)
  have hθβ : Relation.ReflTransGen (Flip (completeDiagram n)) θ β :=
    reachable_openCompleteChain_of_chain_above θ b _ hrowθ hchainθ
  have hηγ : Relation.ReflTransGen (Flip (completeDiagram n)) η γ :=
    reachable_openCompleteChain_of_chain_above η b _ hrowη hchainη
  have hzero : ∀ v, 0 < v.val → v.val < a →
      ¬ (completeDiagram n).edgeData.selected β.val 0 v := by
    intro v _ hva h
    have hbound := (openCompleteChain_row θ b _ hrowθ v).mp h
    change a + m ≤ v.val at hbound
    lia
  have heq : completeExtendAlong ι β (completeRestrictAlong ι γ) = γ :=
    completeExtendAlong_eq_of_outside ι β γ
      (openCompleteChain_outside ι θ η b _ houtside)
  have hβγ := interval_lift_reachable ha hb β hzero hpath
  change Relation.ReflTransGen (Flip (completeDiagram n)) β
    (completeExtendAlong ι β (completeRestrictAlong ι γ)) at hβγ
  rw [heq] at hβγ
  have reverse {σ τ : Orientation (completeDiagram n)}
      (h : Relation.ReflTransGen (Flip (completeDiagram n)) σ τ) :
      Relation.ReflTransGen (Flip (completeDiagram n)) τ σ := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.head (flip_symm _ hs)
  exact hθβ.trans (hβγ.trans (reverse hηγ))

theorem complete_interval_chain_path {n a m : ℕ} (ha : 0 < a) (hb : a + m ≤ n)
    (θ η : Orientation (completeDiagram n))
    (hrowθ : ∀ v, (completeDiagram n).edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hrowη : ∀ v, (completeDiagram n).edgeData.selected η.val 0 v ↔ v = Fin.last n)
    (hchainθ : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected θ.val u v)
    (hchainη : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected η.val u v)
    (houtside : ∀ u v, (¬ ∃ i j,
      intervalEmbed a m ha hb i = u ∧ intervalEmbed a m ha hb j = v) →
      ((completeDiagram n).edgeData.selected θ.val u v ↔
        (completeDiagram n).edgeData.selected η.val u v))
    (hpath : Relation.ReflTransGen (Flip (completeDiagram (m + 1)))
      (completeRestrictAlong (intervalEmbed a m ha hb)
        (openCompleteChain θ (intervalEmbed a m ha hb (Fin.last (m + 1)))
          (intervalEmbed_last_pos ha hb)))
      (completeRestrictAlong (intervalEmbed a m ha hb)
        (openCompleteChain η (intervalEmbed a m ha hb (Fin.last (m + 1)))
          (intervalEmbed_last_pos ha hb)))) :
    Relation.ReflTransGen (Flip (completeDiagram n)) θ η := by
  exact complete_interval_chain_path_of_chain_above ha hb θ η hrowθ hrowη
    (fun u v hbu huv => hchainθ u v
      ((intervalEmbed_last_pos ha hb).trans_le hbu) huv)
    (fun u v hbu huv => hchainη u v
      ((intervalEmbed_last_pos ha hb).trans_le hbu) huv)
    houtside hpath

end VerticalStripLLT.Circular.DiagramProof
