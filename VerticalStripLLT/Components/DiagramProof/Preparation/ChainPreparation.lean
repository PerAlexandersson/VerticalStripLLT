import VerticalStripLLT.Components.DiagramProof.Preparation.PreparationStep
import VerticalStripLLT.Components.DiagramProof.Foundation.CornerTransport

/-! Sweep every inversion out of one corner chain and recover all corner covers. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- The remaining exits from the active chain to chains with smaller terminal. -/
def chainExits (θ : Orientation D) (t : Fin n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => F.terminal hforward p.1 = t ∧
    F.terminal hforward p.2 < t ∧ D.edgeData.selected θ.val p.1 p.2

/-- Finish a single chain sweep, retaining its corner covers and all previously good edges. -/
theorem exists_chainSweep (θ : Orientation D) (t : Fin n)
    (hU : Absorbing (D.edgeData.selected θ.val) (fun u => t < F.terminal hforward u))
    (hC : F.ChainCover hforward θ t) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.ChainCover hforward η t ∧
      Absorbing (D.edgeData.selected η.val) (fun u => t < F.terminal hforward u) ∧
      (∀ u v, F.terminal hforward u = t → D.edgeData.selected η.val u v →
        t ≤ F.terminal hforward v) ∧
      (∀ u v, D.edgeData.selected η.val u v →
        D.edgeData.selected θ.val u v ∨ F.terminal hforward v = t) ∧
      (∀ u v, F.terminal hforward u ≤ F.terminal hforward v →
        D.edgeData.selected θ.val u v → D.edgeData.selected η.val u v) := by
  generalize hN : (F.chainExits hforward θ t).card = N
  induction N using Nat.strong_induction_on generalizing θ with
  | h N ih =>
    by_cases hexit : ∃ u v, F.terminal hforward u = t ∧ F.terminal hforward v < t ∧
        D.edgeData.selected θ.val u v
    · obtain ⟨ξ, hmove, hCξ, hUξ, a, b, c, hat, hbt, hct, _, hsab, hswap⟩ :=
        F.exists_preparationStep hforward θ t hU hC hexit
      have hexits : F.chainExits hforward ξ t = (F.chainExits hforward θ t).erase (a, b) := by
        ext p
        obtain ⟨u, v⟩ := p
        simp only [chainExits, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, hswap]
        have hbne : F.terminal hforward b ≠ t := hbt.ne
        grind
      have hmem : (a, b) ∈ F.chainExits hforward θ t :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hat, hbt, hsab⟩
      have hlt : (F.chainExits hforward ξ t).card < N := by
        rw [← hN, hexits]
        exact Finset.card_erase_lt_of_mem hmem
      obtain ⟨η, hpath, hCη, hUη, hno, hsub, hgood⟩ := ih _ hlt ξ hUξ hCξ rfl
      refine ⟨η, (Relation.ReflTransGen.single hmove).trans hpath, hCη, hUη, hno, ?_, ?_⟩
      · intro u v hs
        rcases hsub u v hs with hs | heq
        · rcases (hswap u v).mp hs with ⟨rfl, rfl⟩ | ⟨hold, _⟩
          · exact Or.inr hct
          · exact Or.inl hold
        · exact Or.inr heq
      · intro u v hle hs
        apply hgood u v hle
        apply (hswap u v).mpr
        refine Or.inr ⟨hs, ?_⟩
        rintro ⟨rfl, rfl⟩
        rw [hat] at hle
        exact not_le_of_gt hbt hle
    · refine ⟨θ, Relation.ReflTransGen.refl, hC, hU, ?_, ?_, ?_⟩
      · intro u v hut huv
        exact le_of_not_gt (fun hvt => hexit ⟨u, v, hut, hvt, huv⟩)
      · intro u v hs
        exact Or.inl hs
      · intro u v _ hs
        exact hs

/-- Complete a chain, allowing other corner covers to disappear temporarily and then recover. -/
theorem exists_prepareChain (θ : Orientation D) (t : Fin n)
    (hU : Absorbing (D.edgeData.selected θ.val) (fun u => t < F.terminal hforward u))
    (hC : F.CommonCover θ) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ F.CommonCover η ∧
      Absorbing (D.edgeData.selected η.val) (fun u => t ≤ F.terminal hforward u) ∧
      Absorbing (D.edgeData.selected η.val) (fun u => t < F.terminal hforward u) ∧
      (∀ u v, F.terminal hforward u = t → D.edgeData.selected η.val u v →
        t ≤ F.terminal hforward v) ∧
      (∀ u v, D.edgeData.selected η.val u v →
        D.edgeData.selected θ.val u v ∨ F.terminal hforward v = t) ∧
      (∀ u v, F.terminal hforward u ≤ F.terminal hforward v →
        D.edgeData.selected θ.val u v → D.edgeData.selected η.val u v) := by
  obtain ⟨η, hpath, hCη, hUη, hno, hsub, hgood⟩ :=
    F.exists_chainSweep hforward θ t hU (fun e he _ => hC e he)
  have hV : Absorbing (D.edgeData.selected η.val) (fun u => t ≤ F.terminal hforward u) := by
    intro u v hs hu
    rcases lt_or_eq_of_le hu with hu | hu
    · exact (hUη hs hu).le
    · exact hno u v hu.symm hs
  refine ⟨η, hpath, ?_, hV, hUη, hno, hsub, hgood⟩
  intro e he
  have hsel : D.edgeData.selected η.val e.tail e.head := by
    apply (mem_fullSelection_iff_selected η e).mp
    apply (corner_mem_iff_of_reachable hpath (F.corner e he)).mp
    exact (F.subset_fullSelection_of_commonCover hforward hC) he
  have hterm : F.terminal hforward e.tail = F.terminal hforward e.head :=
    (F.terminal_eq_iff_mem hforward e).mpr he
  rcases lt_trichotomy (F.terminal hforward e.tail) t with hlt | heq | hgt
  · apply relationCover_of_subrelation_outside_absorbing hV ?_ (hC e he) hsel
      (not_le_of_gt (hterm ▸ hlt))
    intro u v _ hv hs
    exact (hsub u v hs).resolve_right (fun heq => hv heq.ge)
  · exact hCη e he heq
  · apply relationCover_of_subrelation_inside_absorbing hUη ?_ (hC e he) hsel hgt
    intro u v _ hv hs
    exact (hsub u v hs).resolve_right (fun heq => hv.ne' heq)

end

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
