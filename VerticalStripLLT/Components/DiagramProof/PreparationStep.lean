import VerticalStripLLT.Components.DiagramProof.GoodEdges
import VerticalStripLLT.Components.DiagramProof.AbsorbingPaths
import VerticalStripLLT.Components.DiagramProof.OrderedSweep

/-! A preparation move removes the first exit from one corner chain. -/

namespace VerticalStripLLT.Circular.DiagramProof

/-- A short exchange is invisible on intervals disjoint from its retained long. -/
theorem short_swap_agree_on_disjoint_interval {V : Type*} [LinearOrder V]
    {R S : V → V → Prop} {a b c lo hi : V} (hab : a < b) (hbc : b < c)
    (hswap : ∀ u v, S u v ↔
      (u = b ∧ v = c) ∨ (R u v ∧ ¬ (u = a ∧ v = b)))
    (hout : hi ≤ a ∨ c ≤ lo) (u v : V) (hlo : lo ≤ u) (hhi : v ≤ hi) :
    S u v ↔ R u v := by
  rw [hswap]
  rcases hout with hout | hout
  · have hvb : v ≠ b := (hhi.trans_lt (hout.trans_lt hab)).ne
    have hvc : v ≠ c := (hhi.trans_lt (hout.trans_lt (hab.trans hbc))).ne
    simp only [hvb, hvc, and_false, false_or, not_false_eq_true, and_true]
  · have hua : u ≠ a := ((hab.trans hbc).trans_le (hout.trans hlo)).ne.symm
    have hub : u ≠ b := (hbc.trans_le (hout.trans hlo)).ne.symm
    simp only [hua, hub, false_and, false_or, not_false_eq_true, and_true]

namespace CornerFamily

open Classical

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- Only the corners of the chain currently being processed must cover during its sweep. -/
def ChainCover (θ : Orientation D) (t : Fin n) : Prop :=
  ∀ e ∈ F.edges, F.terminal hforward e.tail = t → Cover θ e.tail e.head

/-- Move one inversion, preserving the processed union and all corners of the active chain. -/
theorem exists_preparationStep (θ : Orientation D) (t : Fin n)
    (hU : Absorbing (D.edgeData.selected θ.val) (fun u => t < F.terminal hforward u))
    (hC : F.ChainCover hforward θ t)
    (hexit : ∃ u v, F.terminal hforward u = t ∧ F.terminal hforward v < t ∧
      D.edgeData.selected θ.val u v) :
    ∃ η : Orientation D, Flip D θ η ∧ F.ChainCover hforward η t ∧
      Absorbing (D.edgeData.selected η.val) (fun u => t < F.terminal hforward u) ∧
      ∃ a b c, F.terminal hforward a = t ∧ F.terminal hforward b < t ∧
        F.terminal hforward c = t ∧ F.step a c ∧ D.edgeData.selected θ.val a b ∧
        (∀ u v, D.edgeData.selected η.val u v ↔
          (u = b ∧ v = c) ∨ (D.edgeData.selected θ.val u v ∧ ¬ (u = a ∧ v = b))) := by
  obtain ⟨a, y, hat, hyt, hay⟩ := hexit
  let exits : Finset (Fin n) := Finset.univ.filter fun v =>
    F.terminal hforward v < t ∧ D.edgeData.selected θ.val a v
  have hnonempty : exits.Nonempty := ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyt, hay⟩⟩
  let b := exits.min' hnonempty
  have hb : b ∈ exits := Finset.min'_mem _ _
  have hbt := (Finset.mem_filter.mp hb).2.1
  have hsab := (Finset.mem_filter.mp hb).2.2
  obtain ⟨e, he, het, heh⟩ := hsab
  have hsab : D.edgeData.selected θ.val a b := ⟨e, he, het, heh⟩
  change e.tail = a at het
  change e.head = b at heh
  obtain ⟨c, hcorner, hbc, hct⟩ := F.successor_of_inversion hforward e (by
    simpa only [het, heh, hat] using hbt)
  rw [het] at hcorner hct
  rw [heh] at hbc
  have hab : a < b := θ.selected_lt_of_forward hforward hsab
  have hct' : F.terminal hforward c = t := hct.trans hat
  obtain ⟨f, hf, hft, hfh⟩ := (F.step_iff a c).mp hcorner
  have hac : Cover θ a c := by
    have h := hC f hf (by simpa only [hft] using hat)
    simpa only [hft, hfh] using h
  have hshort : Cover θ a b := by
    apply relationCover_of_first_outside
      (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) hU hsab (not_lt_of_ge hbt.le)
    intro z _ hzb hz haz
    have hzt : F.terminal hforward z ≤ t := le_of_not_gt hz
    rcases lt_or_eq_of_le hzt with hzt | hzt
    · have hzmem : z ∈ exits := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzt, haz⟩
      exact (not_lt_of_ge (Finset.min'_le _ z hzmem)) hzb
    · obtain ⟨g, _, hgt, hgh⟩ := haz
      change g.tail = a at hgt
      change g.head = z at hgh
      have hg := F.mem_of_terminal_eq hforward g (by rw [hgt, hgh, hat, hzt])
      have hzc : z = c := F.step_rightUnique
        ((F.step_iff a z).mpr ⟨g, hg, hgt, hgh⟩) hcorner
      exact (not_lt_of_ge hbc.le) (hzc ▸ hzb)
  obtain ⟨η, hmove, hac', _, hswap⟩ :=
    exists_outgoingSwap_of_covers hforward θ a b c hshort hac hbc
  have hC' : F.ChainCover hforward η t := by
    intro g hg hgt
    have hstep : F.step g.tail g.head := (F.step_iff _ _).mpr ⟨g, hg, rfl, rfl⟩
    rcases F.step_intervals hforward hcorner hstep (hat.trans hgt.symm) with hright | hleft | heq
    · apply (relationCover_congr_on_interval
        (fun {_ _} hs => θ.selected_lt_of_forward hforward hs)
        (fun {_ _} hs => η.selected_lt_of_forward hforward hs)
        (lo := g.tail) (hi := g.head) ?_ le_rfl le_rfl).mp (hC g hg hgt)
      intro u v hu hv
      exact (short_swap_agree_on_disjoint_interval hab hbc hswap (Or.inr hright) u v hu hv).symm
    · apply (relationCover_congr_on_interval
        (fun {_ _} hs => θ.selected_lt_of_forward hforward hs)
        (fun {_ _} hs => η.selected_lt_of_forward hforward hs)
        (lo := g.tail) (hi := g.head) ?_ le_rfl le_rfl).mp (hC g hg hgt)
      intro u v hu hv
      exact (short_swap_agree_on_disjoint_interval hab hbc hswap (Or.inl hleft) u v hu hv).symm
    · simpa only [heq.1, heq.2] using hac'
  have hU' : Absorbing (D.edgeData.selected η.val) (fun u => t < F.terminal hforward u) := by
    intro u v hs hu
    rcases (hswap u v).mp hs with ⟨rfl, rfl⟩ | ⟨hold, _⟩
    · exact (not_lt_of_ge hbt.le hu).elim
    · exact hU hold hu
  exact ⟨η, hmove, hC', hU', a, b, c, hat, hbt, hct', hcorner, hsab, hswap⟩

end CornerFamily

end VerticalStripLLT.Circular.DiagramProof
