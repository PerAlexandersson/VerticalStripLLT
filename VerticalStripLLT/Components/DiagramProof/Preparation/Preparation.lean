import VerticalStripLLT.Components.DiagramProof.Preparation.ChainPreparation
import VerticalStripLLT.Components.DiagramProof.Foundation.WeakBlocks

/-!
# Ordered preparation of all corner chains

We process terminal labels in decreasing order. The inner induction counts exits
from one chain; the outer induction decreases the number of unprocessed labels.
Other corners may temporarily become redundant, but every completed chain sweep
recovers the common-cover condition. All originally good edges are preserved.
-/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- Every chain with terminal label at least `k` has already been prepared. -/
def PreparedAbove (θ : Orientation D) (k : ℕ) : Prop :=
  ∀ u v, D.edgeData.selected θ.val u v → k ≤ (F.terminal hforward u).val →
    F.terminal hforward u ≤ F.terminal hforward v

/-- The full ordered path, including preservation of all already-good selected edges. -/
theorem exists_preparation_below (k : ℕ) (θ : Orientation D) (hC : F.CommonCover θ)
    (hready : F.PreparedAbove hforward θ k) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hforward η ∧
      (∀ u v, F.terminal hforward u ≤ F.terminal hforward v →
        D.edgeData.selected θ.val u v → D.edgeData.selected η.val u v) := by
  induction k generalizing θ with
  | zero =>
    refine ⟨θ, Relation.ReflTransGen.refl, ⟨F.subset_fullSelection_of_commonCover hforward hC,
      ?_⟩, fun _ _ _ hs => hs⟩
    intro e he
    have hle := hready e.tail e.head ((mem_fullSelection_iff_selected θ e).mp he) (Nat.zero_le _)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inr hlt
    · exact Or.inl (F.mem_of_terminal_eq hforward e heq)
  | succ k ih =>
    by_cases hk : k < n
    · let t : Fin n := ⟨k, hk⟩
      have hU : Absorbing (D.edgeData.selected θ.val) (fun u => t < F.terminal hforward u) := by
        intro u v hs hu
        have hku : k + 1 ≤ (F.terminal hforward u).val := hu
        exact hu.trans_le (hready u v hs hku)
      obtain ⟨ξ, hp, hCξ, _, hUξ, hno, hsub, hgood⟩ :=
        F.exists_prepareChain hforward θ t hU hC
      have hreadyξ : F.PreparedAbove hforward ξ k := by
        intro u v hs hu
        have htu : t ≤ F.terminal hforward u := hu
        rcases lt_or_eq_of_le htu with htu | htu
        · have htv := hUξ hs htu
          have hold := (hsub u v hs).resolve_right (fun h => htv.ne' h)
          exact hready u v hold htu
        · rw [← htu]
          exact hno u v htu.symm hs
      obtain ⟨η, hrest, hanchor, hkeep⟩ := ih ξ hCξ hreadyξ
      exact ⟨η, hp.trans hrest, hanchor, fun u v hle hs =>
        hkeep u v hle (hgood u v hle hs)⟩
    · apply ih θ hC
      intro u v _ hu
      exact (hk (hu.trans_lt (F.terminal hforward u).isLt)).elim

/-- Every common-cover state reaches an anchor by actual flips. -/
theorem exists_preparation (θ : Orientation D) (hC : F.CommonCover θ) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.Anchor hforward η ∧
      (∀ u v, F.terminal hforward u ≤ F.terminal hforward v →
        D.edgeData.selected θ.val u v → D.edgeData.selected η.val u v) := by
  apply F.exists_preparation_below hforward n θ hC
  intro u v _ hu
  exact (not_le_of_gt (F.terminal hforward u).isLt hu).elim

/-- Preparation preserves the actual whole component, total selected count and all weak blocks. -/
theorem exists_anchor_in_component (θ : Orientation D) (hC : F.CommonCover θ) :
    ∃ η ∈ flipComponent D θ, F.Anchor hforward η ∧ totalSelected η = totalSelected θ ∧
      (∀ u v, WeakReach η u v ↔ WeakReach θ u v) ∧
      (∀ e ∈ fullSelection θ, F.GoodEdge hforward e → e ∈ fullSelection η) := by
  obtain ⟨η, hp, hanchor, hkeep⟩ := F.exists_preparation hforward θ hC
  refine ⟨η, mem_flipComponent_iff.mpr hp, hanchor,
    (totalSelected_eq_of_reachable hp).symm, fun u v => (weakReach_iff_of_reachable hp u v).symm,
    ?_⟩
  intro e he hgood
  apply (mem_fullSelection_iff_selected η e).mpr
  exact hkeep e.tail e.head (F.terminal_le_of_good hforward hgood)
    ((mem_fullSelection_iff_selected θ e).mp he)

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
