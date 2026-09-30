import VerticalStripLLT.Components.DiagramProof.ParallelPacking
import VerticalStripLLT.Components.DiagramProof.TerminalClique

/-! Basic identities for the occupancy vector of an anchor. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical
open scoped BigOperators

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- Occupancies partition the full selected edge set by terminal labels. -/
theorem sum_occupancy (θ : Orientation D) :
    (∑ p : Fin n × Fin n, F.occupancy hforward θ p) = totalSelected θ := by
  classical
  have hcard : (fullSelection θ).card =
      ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)),
        ((fullSelection θ).filter (fun e => F.copyLabel hforward e = p)).card :=
    Finset.card_eq_sum_card_fiberwise (s := fullSelection θ)
      (t := Finset.univ) (f := F.copyLabel hforward) (by
        intro e he
        exact Finset.mem_univ _)
  unfold occupancy totalSelected
  convert hcard.symm using 1

/-- Diagonal occupancies are fixed across anchors: they count retained corners. -/
theorem occupancy_diagonal_eq (θ η : Orientation D)
    (hθ : F.Anchor hforward θ) (hη : F.Anchor hforward η) (t : Fin n) :
    F.occupancy hforward θ (t, t) = F.occupancy hforward η (t, t) := by
  classical
  have hfilter (σ : Orientation D) (hσ : F.Anchor hforward σ) :
      (fullSelection σ).filter
          (fun e => F.copyLabel hforward e = (t, t)) =
        (F.edges).filter (fun e => F.copyLabel hforward e = (t, t)) := by
    ext e
    constructor
    · intro he
      have hlabel := (Finset.mem_filter.mp he).2
      have htail := congrArg Prod.fst hlabel
      have hhead := congrArg Prod.snd hlabel
      change F.terminal hforward e.tail = t at htail
      change F.terminal hforward e.head = t at hhead
      have hdiag : F.terminal hforward e.tail = F.terminal hforward e.head :=
        htail.trans hhead.symm
      exact Finset.mem_filter.mpr ⟨
        (F.terminal_eq_iff_mem hforward e).mp hdiag, hlabel⟩
    · intro he
      exact Finset.mem_filter.mpr ⟨hσ.1 (Finset.mem_filter.mp he).1,
        (Finset.mem_filter.mp he).2⟩
  unfold occupancy
  rw [hfilter θ hθ, hfilter η hη]

/-- Every anchor occupancy is bounded by the number of good copies of its label. -/
theorem occupancy_le_capacity (θ : Orientation D) (hθ : F.Anchor hforward θ)
    (p : Fin n × Fin n) :
    F.occupancy hforward θ p ≤
      ((F.goodEdges hforward).filter
        (fun e => F.copyLabel hforward e = p)).card := by
  classical
  unfold occupancy
  apply Finset.card_le_card
  intro e he
  obtain ⟨hefull, hlabel⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨
    (F.mem_goodEdges hforward e).mpr (hθ.2 e hefull), hlabel⟩

/-- A strict occupancy surplus supplies a terminal copy of that label. -/
theorem exists_terminalEdge_of_occupancy_gt (c : Edge D.area)
    (hterm : ∀ v, c.tail < F.terminal hforward v ∧
      F.terminal hforward v ≤ c.head)
    (θ τ : Orientation D) (hθ : F.Anchor hforward θ)
    (hτ : F.Anchor hforward τ) (p : Fin n × Fin n)
    (hgt : F.occupancy hforward τ p < F.occupancy hforward θ p) :
    ∃ e ∈ F.terminalEdges hforward, F.copyLabel hforward e = p := by
  classical
  have hpos : 0 < F.occupancy hforward θ p :=
    lt_of_le_of_lt (Nat.zero_le _) hgt
  unfold occupancy at hpos
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  obtain ⟨haθ, hlabel⟩ := Finset.mem_filter.mp ha
  by_cases hac : a ∈ F.edges
  · have hdiag : F.copyLabel hforward a =
        (F.terminal hforward a.tail, F.terminal hforward a.tail) := by
      have hteq := (F.terminal_eq_iff_mem hforward a).mpr hac
      simp only [copyLabel]
      exact Prod.ext rfl hteq.symm
    have hpdiag : p =
        (F.terminal hforward a.tail, F.terminal hforward a.tail) :=
      hlabel.symm.trans hdiag
    rw [hpdiag, F.occupancy_diagonal_eq hforward θ τ hθ hτ] at hgt
    exact (Nat.lt_irrefl _ hgt).elim
  · have hinc : F.terminal hforward a.tail < F.terminal hforward a.head := by
      rcases hθ.2 a haθ with hac' | hinc
      · exact (hac hac').elim
      · exact hinc
    obtain ⟨e, he, het, heh⟩ := F.exists_terminalEdge_of_last_clique
      hforward c hterm a.tail a.head hinc
    refine ⟨e, he, ?_⟩
    have hcopy : F.copyLabel hforward e =
        (F.terminal hforward a.tail, F.terminal hforward a.head) := by
      apply Prod.ext
      · change F.terminal hforward e.tail = F.terminal hforward a.tail
        rw [het, F.terminal_idempotent]
      · change F.terminal hforward e.head = F.terminal hforward a.head
        rw [heh, F.terminal_idempotent]
    exact hcopy.trans hlabel

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
