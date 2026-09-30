import VerticalStripLLT.Components.DiagramProof.IntervalPaths
import VerticalStripLLT.Components.DiagramProof.SubdiagramCounts

/-! Apply the smaller complete-diagram theorem after opening and restricting an interval. -/

namespace VerticalStripLLT.Circular.DiagramProof

/-- Equal global counts and equal exterior give equal counts in the opened restrictions. -/
theorem openCompleteChain_interval_totalSelected_eq {n a m : ℕ}
    (ha : 0 < a) (hb : a + m ≤ n) (θ η : Orientation (completeDiagram n))
    (hrowθ : ∀ v, (completeDiagram n).edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hrowη : ∀ v, (completeDiagram n).edgeData.selected η.val 0 v ↔ v = Fin.last n)
    (hchainθ : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected θ.val u v)
    (hchainη : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected η.val u v)
    (htotal : totalSelected θ = totalSelected η)
    (houtside : ∀ u v, (¬ ∃ i j,
      intervalEmbed a m ha hb i = u ∧ intervalEmbed a m ha hb j = v) →
      ((completeDiagram n).edgeData.selected θ.val u v ↔
        (completeDiagram n).edgeData.selected η.val u v)) :
    totalSelected (completeRestrictAlong (intervalEmbed a m ha hb)
      (openCompleteChain θ (intervalEmbed a m ha hb (Fin.last (m + 1)))
        (intervalEmbed_last_pos ha hb))) =
    totalSelected (completeRestrictAlong (intervalEmbed a m ha hb)
      (openCompleteChain η (intervalEmbed a m ha hb (Fin.last (m + 1)))
        (intervalEmbed_last_pos ha hb))) := by
  let ι := intervalEmbed a m ha hb
  let b := ι (Fin.last (m + 1))
  let β := openCompleteChain θ b (intervalEmbed_last_pos ha hb)
  let γ := openCompleteChain η b (intervalEmbed_last_pos ha hb)
  have hθβ := totalSelected_eq_of_reachable
    (reachable_openCompleteChain θ b (intervalEmbed_last_pos ha hb) hrowθ hchainθ)
  have hηγ := totalSelected_eq_of_reachable
    (reachable_openCompleteChain η b (intervalEmbed_last_pos ha hb) hrowη hchainη)
  exact completeRestrictAlong_totalSelected_eq ι β γ (hθβ.symm.trans (htotal.trans hηγ))
    (openCompleteChain_outside ι θ η b _ houtside)

/-- The smaller active-layer theorem supplies the local path in CC3. -/
theorem complete_interval_chain_path_of_equal_count {n a m : ℕ}
    (ha : 0 < a) (hb : a + m ≤ n)
    (hsmall : ∀ α β : Orientation (completeDiagram (m + 1)),
      SelectedConnected α → Cover α 0 (Fin.last (m + 1)) →
      SelectedConnected β → Cover β 0 (Fin.last (m + 1)) →
      totalSelected α = totalSelected β →
      Relation.ReflTransGen (Flip (completeDiagram (m + 1))) α β)
    (θ η : Orientation (completeDiagram n))
    (hrowθ : ∀ v, (completeDiagram n).edgeData.selected θ.val 0 v ↔ v = Fin.last n)
    (hrowη : ∀ v, (completeDiagram n).edgeData.selected η.val 0 v ↔ v = Fin.last n)
    (hchainθ : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected θ.val u v)
    (hchainη : ∀ u v : Fin (n + 1), 0 < u → u.val + 1 = v.val →
      (completeDiagram n).edgeData.selected η.val u v)
    (htotal : totalSelected θ = totalSelected η)
    (houtside : ∀ u v, (¬ ∃ i j,
      intervalEmbed a m ha hb i = u ∧ intervalEmbed a m ha hb j = v) →
      ((completeDiagram n).edgeData.selected θ.val u v ↔
        (completeDiagram n).edgeData.selected η.val u v)) :
    Relation.ReflTransGen (Flip (completeDiagram n)) θ η := by
  apply complete_interval_chain_path ha hb θ η hrowθ hrowη hchainθ hchainη houtside
  have hθ := openCompleteChain_interval_connected_cover ha hb θ hrowθ hchainθ
  have hη := openCompleteChain_interval_connected_cover ha hb η hrowη hchainη
  exact hsmall _ _ hθ.1 hθ.2 hη.1 hη.2
    (openCompleteChain_interval_totalSelected_eq ha hb θ η hrowθ hrowη hchainθ hchainη
      htotal houtside)

end VerticalStripLLT.Circular.DiagramProof
