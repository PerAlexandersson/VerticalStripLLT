import VerticalStripLLT.Components.DiagramProof.Corners.CopyGeometry
import VerticalStripLLT.Components.DiagramProof.Foundation.ShortFlip

/-! Auxiliary short-edge links and the ordered path of good copies for a chain pair. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D)

/-- One auxiliary short-edge step `ab → bc`, retaining the corner `ac`. -/
def ShortLink (e f : Edge D.area) : Prop := e.head = f.tail ∧ F.step e.tail f.head

/-- Consecutive good positions `ab, cd`, with retained crossing corners `ac, bd`. -/
def CopyLink (e f : Edge D.area) : Prop :=
  F.step e.tail f.tail ∧ F.step e.head f.head ∧ e.head < f.tail

theorem shortLink_rightUnique : Relator.RightUnique F.ShortLink := by
  intro e f g hef heg
  apply D.endpointEmbedding.injective
  exact Prod.ext (hef.1.symm.trans heg.1) (F.step_rightUnique hef.2 heg.2)

theorem shortLink_leftUnique : Relator.LeftUnique F.ShortLink := by
  intro e f g heg hfg
  apply D.endpointEmbedding.injective
  exact Prod.ext (F.step_leftUnique heg.2 hfg.2) (heg.1.trans hfg.1.symm)

/-- Neither short copy of a crossing can itself be a retained corner. -/
theorem copyLink_not_mem {e f : Edge D.area} (h : F.CopyLink e f) :
    e ∉ F.edges ∧ f ∉ F.edges := by
  constructor
  · intro he
    have he' : F.step e.tail e.head := (F.step_iff _ _).mpr ⟨e, he, rfl, rfl⟩
    exact h.2.2.ne (F.step_rightUnique he' h.1)
  · intro hf
    have hf' : F.step f.tail f.head := (F.step_iff _ _).mpr ⟨f, hf, rfl, rfl⟩
    exact h.2.2.ne (F.step_leftUnique h.2.1 hf')

variable (hforward : Forward D)

include hforward in
theorem shortLink_tail_lt {e f : Edge D.area} (h : F.ShortLink e f) : e.tail < f.tail :=
  (hforward e).trans_eq h.1

theorem shortLink_terminals {e f : Edge D.area} (h : F.ShortLink e f) :
    F.terminal hforward e.tail = F.terminal hforward f.head ∧
      F.terminal hforward e.head = F.terminal hforward f.tail :=
  ⟨F.terminal_eq_of_step hforward h.2, congrArg (F.terminal hforward) h.1⟩

/-- Every nonfinal normal position has its unique next short-edge position. -/
theorem exists_shortSuccessor (e : Edge D.area) (he : e ∉ F.edges)
    (hne : e.tail ≠ F.terminal hforward e.tail) :
    ∃ f : Edge D.area, F.ShortLink e f ∧ f ∉ F.edges := by
  obtain ⟨c, hac⟩ := F.exists_successor hforward hne
  have hbc := F.head_lt_of_chain_reachable hforward e he
    (Relation.ReflTransGen.single hac) (F.step_forward hforward hac)
  obtain ⟨_, f, _, _, _, _, hft, hfh⟩ :=
    exists_normalShortEdges_of_selected (D := F.diagram) hforward (F.chains hforward)
      e.tail e.head c hac (hforward e) hbc
  have hlink : F.ShortLink e f := ⟨hft.symm, hfh ▸ hac⟩
  refine ⟨f, hlink, ?_⟩
  intro hf
  have ht := F.shortLink_terminals hforward hlink
  have hsame := (F.terminal_eq_iff_mem hforward f).mpr hf
  exact he ((F.terminal_eq_iff_mem hforward e).mp (ht.1.trans (hsame.symm.trans ht.2.symm)))

/-- Every good copy except the last has a next good copy in the same chain pair. -/
theorem exists_copySuccessor (e : Edge D.area)
    (he : F.terminal hforward e.tail < F.terminal hforward e.head)
    (hne : e.tail ≠ F.terminal hforward e.tail) :
    ∃ f : Edge D.area, F.CopyLink e f ∧
      F.terminal hforward e.tail = F.terminal hforward f.tail ∧
      F.terminal hforward e.head = F.terminal hforward f.head := by
  have hen : e ∉ F.edges := fun h => he.ne ((F.terminal_eq_iff_mem hforward e).mpr h)
  obtain ⟨g, heg, hgn⟩ := F.exists_shortSuccessor hforward e hen hne
  have htg := F.shortLink_terminals hforward heg
  have hginv : F.terminal hforward g.head < F.terminal hforward g.tail := by
    rw [← htg.1, ← htg.2]
    exact he
  have hgne : g.tail ≠ F.terminal hforward g.tail :=
    ((hforward g).trans ((F.le_terminal hforward g.head).trans_lt hginv)).ne
  obtain ⟨f, hgf, _⟩ := F.exists_shortSuccessor hforward g hgn hgne
  have htf := F.shortLink_terminals hforward hgf
  refine ⟨f, ⟨?_, ?_, ?_⟩, htg.1.trans htf.2, htg.2.trans htf.1⟩
  · exact hgf.1 ▸ heg.2
  · exact heg.1.symm ▸ hgf.2
  · exact heg.1.symm ▸ hgf.1 ▸ hforward g

/-- All good copies between a fixed ordered pair of chains lie on one increasing path. -/
theorem copy_reachable_of_tail_le (e f : Edge D.area)
    (he : F.terminal hforward e.tail < F.terminal hforward e.head)
    (ht : F.terminal hforward e.tail = F.terminal hforward f.tail)
    (hh : F.terminal hforward e.head = F.terminal hforward f.head)
    (hle : e.tail ≤ f.tail) : Relation.ReflTransGen F.CopyLink e f := by
  generalize hN : n - e.tail.val = N
  induction N using Nat.strong_induction_on generalizing e with
  | h N ih =>
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hne : e.tail ≠ F.terminal hforward e.tail := by
        intro h
        have hf := F.le_terminal hforward f.tail
        rw [← ht, ← h] at hf
        exact not_le_of_gt hlt hf
      obtain ⟨g, heg, htg, hhg⟩ := F.exists_copySuccessor hforward e he hne
      have hgle : g.tail ≤ f.tail := by
        have hp := (F.reachable_iff hforward e.tail f.tail).mpr ⟨hle, ht⟩
        rcases hp.cases_head with heq | ⟨v, hv, hrest⟩
        · exact (hlt.ne heq).elim
        · have hvEq : v = g.tail := F.step_rightUnique hv heg.1
          exact hvEq ▸ reachable_le (fun {_ _} h => F.step_forward hforward h) hrest
      have hmeasure : n - g.tail.val < N := by
        have hltg := F.step_forward hforward heg.1
        have hbound := g.tail.isLt
        change e.tail.val < g.tail.val at hltg
        lia
      have hg : F.terminal hforward g.tail < F.terminal hforward g.head := by
        rw [← htg, ← hhg]
        exact he
      exact (ih _ hmeasure g hg (htg.symm.trans ht) (hhg.symm.trans hh) hgle rfl).head heg
    · have hef := F.edge_eq_of_tail_and_head_terminal_eq hforward e f heq hh
      subst f
      exact Relation.ReflTransGen.refl

/-- The last copy of an ordered chain pair starts at its smaller terminal. -/
theorem exists_lastCopy (e : Edge D.area)
    (he : F.terminal hforward e.tail < F.terminal hforward e.head) :
    ∃ f : Edge D.area, Relation.ReflTransGen F.CopyLink e f ∧
      f.tail = F.terminal hforward e.tail ∧
      F.terminal hforward f.head = F.terminal hforward e.head := by
  generalize hN : n - e.tail.val = N
  induction N using Nat.strong_induction_on generalizing e with
  | h N ih =>
    by_cases htail : e.tail = F.terminal hforward e.tail
    · exact ⟨e, Relation.ReflTransGen.refl, htail, rfl⟩
    · obtain ⟨g, heg, htg, hhg⟩ := F.exists_copySuccessor hforward e he htail
      have hg : F.terminal hforward g.tail < F.terminal hforward g.head := by
        rw [← htg, ← hhg]
        exact he
      have hmeasure : n - g.tail.val < N := by
        have hltg := F.step_forward hforward heg.1
        have hbound := g.tail.isLt
        change e.tail.val < g.tail.val at hltg
        lia
      obtain ⟨f, hgf, hft, hfh⟩ := ih _ hmeasure g hg rfl
      exact ⟨f, hgf.head heg, hft.trans htg.symm, hfh.trans hhg.symm⟩

/-- Good copies of one terminal pair connect by neighboring moves in either direction. -/
theorem copy_reachable_undirected (e f : Edge D.area)
    (he : F.terminal hforward e.tail < F.terminal hforward e.head)
    (ht : F.terminal hforward e.tail = F.terminal hforward f.tail)
    (hh : F.terminal hforward e.head = F.terminal hforward f.head) :
    Relation.ReflTransGen (Relation.SymmGen F.CopyLink) e f := by
  rcases le_total e.tail f.tail with hle | hle
  · exact Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) _ _
      (F.copy_reachable_of_tail_le hforward e f he ht hh hle)
  · have hf : F.terminal hforward f.tail < F.terminal hforward f.head := by
      rw [← ht, ← hh]
      exact he
    have hp := F.copy_reachable_of_tail_le hforward f e hf ht.symm hh.symm hle
    clear he ht hh hle hf
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.head (Or.inr hs)

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
