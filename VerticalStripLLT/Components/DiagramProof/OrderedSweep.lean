import VerticalStripLLT.Components.DiagramProof.IncomingFlip
import Mathlib.Data.Finset.Max

/-!
# Ordered outgoing and incoming sweeps

We repeatedly move the least remaining outgoing neighbor across a retained cover.
The finite induction uses the number of remaining neighbors, not a search of a
flip component. Reversing the order gives the incoming sweep. Both are finally
instantiated with actual orientations and actual flips.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {V : Type*} [LinearOrder V]

/-- Sweep all selected edges from `a` to vertices below `b` across the retained edge `ac`. -/
def outgoingSweepRelation (R : V → V → Prop) (a b c u v : V) : Prop :=
  (a < u ∧ u < b ∧ v = c ∧ R a u) ∨ (R u v ∧ ¬ (u = a ∧ v < b))

/-- The reverse-order incoming sweep removes edges into `d` from vertices above `c`. -/
def incomingSweepRelation (R : V → V → Prop) (b c d u v : V) : Prop :=
  outgoingSweepRelation (V := OrderDual V) (Function.swap R) d c b v u

/-- Explicit original-order form of the reverse-order sweep. -/
theorem incomingSweepRelation_iff (R : V → V → Prop) (b c d u v : V) :
    incomingSweepRelation R b c d u v ↔
      (v < d ∧ c < v ∧ u = b ∧ R v d) ∨ (R u v ∧ ¬ (v = d ∧ c < u)) := Iff.rfl

theorem outgoingSweepRelation_step {R S : V → V → Prop} {a b c w : V}
    (haw : a < w) (hwb : w < b) (hbc : b < c)
    (hsel : R a w)
    (hstep : ∀ u v, S u v ↔ (u = w ∧ v = c) ∨ (R u v ∧ ¬ (u = a ∧ v = w)))
    (u v : V) :
    outgoingSweepRelation S a b c u v ↔ outgoingSweepRelation R a b c u v := by
  simp only [outgoingSweepRelation, hstep]
  have hawne : a ≠ w := haw.ne
  grind

theorem outgoingSweepRelation_agree_above {R : V → V → Prop} {a b c u v : V}
    (hab : a < b) (hbu : b ≤ u) : outgoingSweepRelation R a b c u v ↔ R u v := by
  have hnotub : ¬ u < b := not_lt_of_ge hbu
  have hne : u ≠ a := (hab.trans_le hbu).ne.symm
  simp only [outgoingSweepRelation, hnotub, hne, false_and, and_false, false_or,
    not_false_eq_true, and_true]

/-- The still-unmoved outgoing neighbors in a sweep. -/
def sweepExits [Fintype V] (R : V → V → Prop) (a b : V) : Finset V :=
  Finset.univ.filter fun v => v < b ∧ R a v

/-- Each sweep step retains its pivot, cover witnesses and exact endpoint relation for replay. -/
def OutgoingSweepStep {State : Type*} (selected : State → V → V → Prop)
    (step : State → State → Prop) (a b c : V) (θ η : State) : Prop :=
  ∃ w, a < w ∧ w < b ∧ step θ η ∧
    RelationCover (selected θ) a w ∧ RelationCover (selected θ) a c ∧
    RelationCover (selected η) a c ∧ RelationCover (selected η) w c ∧
    (∀ u v, selected η u v ↔
      (u = w ∧ v = c) ∨ (selected θ u v ∧ ¬ (u = a ∧ v = w)))

/-- A finite ordered sweep for any state system with the proved two-source-cover move. -/
theorem exists_orderedOutgoingSweep_trace [Fintype V] {State : Type*}
    (selected : State → V → V → Prop) (step : State → State → Prop)
    (hforward : ∀ θ ⦃u v⦄, selected θ u v → u < v)
    (hstep : ∀ θ a b c, RelationCover (selected θ) a b →
      RelationCover (selected θ) a c → b < c →
      ∃ η, step θ η ∧ RelationCover (selected η) a c ∧
        (∀ u v, selected η u v ↔
          (u = b ∧ v = c) ∨ (selected θ u v ∧ ¬ (u = a ∧ v = b))))
    (θ : State) (a b c : V) (hab : a < b) (hbc : b < c)
    (hac : RelationCover (selected θ) a c) :
    ∃ η, Relation.ReflTransGen (OutgoingSweepStep selected step a b c) θ η ∧
      RelationCover (selected η) a c ∧
      (∀ u v, selected η u v ↔ outgoingSweepRelation (selected θ) a b c u v) := by
  suffices h : ∀ N, ∀ ξ : State, (sweepExits (selected ξ) a b).card = N →
      RelationCover (selected ξ) a c →
      ∃ η, Relation.ReflTransGen (OutgoingSweepStep selected step a b c) ξ η ∧
        RelationCover (selected η) a c ∧
        (∀ u v, selected η u v ↔ outgoingSweepRelation (selected ξ) a b c u v) from
    h _ θ rfl hac
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro ξ hN hac
    by_cases hempty : sweepExits (selected ξ) a b = ∅
    · have hnone (v : V) (hvb : v < b) : ¬ selected ξ a v := by
        intro hs
        have hm : v ∈ sweepExits (selected ξ) a b :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvb, hs⟩
        rw [hempty] at hm
        exact Finset.notMem_empty _ hm
      refine ⟨ξ, Relation.ReflTransGen.refl, hac, ?_⟩
      intro u v
      constructor
      · intro hs
        refine Or.inr ⟨hs, ?_⟩
        rintro ⟨rfl, hvb⟩
        exact hnone v hvb hs
      · rintro (⟨_, hub, _, hau⟩ | ⟨huv, _⟩)
        · exact (hnone u hub hau).elim
        · exact huv
    · have hnonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      let w := (sweepExits (selected ξ) a b).min' hnonempty
      have hw : w ∈ sweepExits (selected ξ) a b := Finset.min'_mem _ _
      have hwb : w < b := (Finset.mem_filter.mp hw).2.1
      have haw : selected ξ a w := (Finset.mem_filter.mp hw).2.2
      have hav : a < w := hforward ξ haw
      have hcover : RelationCover (selected ξ) a w := by
        apply relationCover_of_first_outgoing (hforward ξ) haw
        intro z _ hzw haz
        have hz : z ∈ sweepExits (selected ξ) a b :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzw.trans hwb, haz⟩
        exact (not_lt_of_ge (Finset.min'_le _ z hz)) hzw
      obtain ⟨ξ', hmove, hac', hswap⟩ := hstep ξ a w c hcover hac (hwb.trans hbc)
      have hexits : sweepExits (selected ξ') a b = (sweepExits (selected ξ) a b).erase w := by
        ext z
        simp only [sweepExits, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, hswap]
        have hne : a ≠ w := hav.ne
        grind
      have hlt : (sweepExits (selected ξ') a b).card < N := by
        rw [← hN, hexits]
        exact Finset.card_erase_lt_of_mem hw
      obtain ⟨η, hpath, hfinalCover, hfinal⟩ := ih _ hlt ξ' rfl hac'
      have hshort := (relationCover_short_swap (hforward ξ)
        (hwb.trans hbc) hcover hac hswap).2.1
      have htrace : OutgoingSweepStep selected step a b c ξ ξ' :=
        ⟨w, hav, hwb, hmove, hcover, hac, hac', hshort, hswap⟩
      refine ⟨η, (Relation.ReflTransGen.single htrace).trans hpath, hfinalCover, ?_⟩
      intro u v
      exact (hfinal u v).trans (outgoingSweepRelation_step hav hwb hbc haw hswap u v)

theorem outgoingSweepTrace_forget {State : Type*} (selected : State → V → V → Prop)
    (step : State → State → Prop) (a b c : V) {θ η : State}
    (h : Relation.ReflTransGen (OutgoingSweepStep selected step a b c) θ η) :
    Relation.ReflTransGen step θ η := by
  apply Relation.ReflTransGen.mono ?_ _ _ h
  rintro ξ ξ' ⟨w, _, _, hmove, _⟩
  exact hmove

/-- Forget the stored sweep pivots when only an actual path and its endpoint are needed. -/
theorem exists_orderedOutgoingSweep [Fintype V] {State : Type*}
    (selected : State → V → V → Prop) (step : State → State → Prop)
    (hforward : ∀ θ ⦃u v⦄, selected θ u v → u < v)
    (hstep : ∀ θ a b c, RelationCover (selected θ) a b →
      RelationCover (selected θ) a c → b < c →
      ∃ η, step θ η ∧ RelationCover (selected η) a c ∧
        (∀ u v, selected η u v ↔
          (u = b ∧ v = c) ∨ (selected θ u v ∧ ¬ (u = a ∧ v = b))))
    (θ : State) (a b c : V) (hab : a < b) (hbc : b < c)
    (hac : RelationCover (selected θ) a c) :
    ∃ η, Relation.ReflTransGen step θ η ∧ RelationCover (selected η) a c ∧
      (∀ u v, selected η u v ↔ outgoingSweepRelation (selected θ) a b c u v) := by
  obtain ⟨η, hpath, hcover, hfinal⟩ :=
    exists_orderedOutgoingSweep_trace selected step hforward hstep θ a b c hab hbc hac
  exact ⟨η, outgoingSweepTrace_forget selected step a b c hpath, hcover, hfinal⟩

variable {n : ℕ} {D : Diagram n}

/-- The outgoing sweep with its complete actual-flip trace retained for restoration. -/
theorem exists_outgoingSweep_trace (hforward : Forward D) (θ : Orientation D)
    (a b c : Fin n) (hab : a < b) (hbc : b < c) (hac : Cover θ a c) :
    ∃ η : Orientation D,
      Relation.ReflTransGen
        (OutgoingSweepStep (fun ξ : Orientation D => D.edgeData.selected ξ.val) (Flip D) a b c)
        θ η ∧ Cover η a c ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        outgoingSweepRelation (D.edgeData.selected θ.val) a b c u v) := by
  apply exists_orderedOutgoingSweep_trace
    (fun ξ : Orientation D => D.edgeData.selected ξ.val) (Flip D)
    (fun ξ {_ _} hs => ξ.selected_lt_of_forward hforward hs) ?_ θ a b c hab hbc hac
  intro ξ x y z hxy hxz hyz
  obtain ⟨η, hmove, hlong, _, hswap⟩ :=
    exists_outgoingSwap_of_covers hforward ξ x y z hxy hxz hyz
  exact ⟨η, hmove, hlong, hswap⟩

/-- Actual outgoing flips sweep the entire initial neighbor interval in increasing order. -/
theorem exists_outgoingSweep (hforward : Forward D) (θ : Orientation D)
    (a b c : Fin n) (hab : a < b) (hbc : b < c) (hac : Cover θ a c) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ Cover η a c ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        outgoingSweepRelation (D.edgeData.selected θ.val) a b c u v) := by
  obtain ⟨η, htrace, hcover, hrel⟩ :=
    exists_outgoingSweep_trace hforward θ a b c hab hbc hac
  exact ⟨η, outgoingSweepTrace_forget _ _ a b c htrace, hcover, hrel⟩

/-- Retain the decreasing incoming sweep as an outgoing trace in the dual order. -/
theorem exists_incomingSweep_trace (hforward : Forward D) (θ : Orientation D)
    (b c d : Fin n) (hbc : b < c) (hcd : c < d) (hbd : Cover θ b d) :
    ∃ η : Orientation D,
      Relation.ReflTransGen
        (OutgoingSweepStep (V := OrderDual (Fin n))
          (fun ξ : Orientation D => Function.swap (D.edgeData.selected ξ.val)) (Flip D) d c b)
        θ η ∧ Cover η b d ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        incomingSweepRelation (D.edgeData.selected θ.val) b c d u v) := by
  have hs := exists_orderedOutgoingSweep_trace (V := OrderDual (Fin n))
    (fun ξ : Orientation D => Function.swap (D.edgeData.selected ξ.val)) (Flip D)
    (fun ξ {_ _} h => ξ.selected_lt_of_forward hforward h) ?_ θ d c b hcd hbc
    ((relationCover_dual (V := Fin n) b d).mpr hbd)
  · obtain ⟨η, hpath, hcover, hfinal⟩ := hs
    exact ⟨η, hpath, (relationCover_dual (V := Fin n) b d).mp hcover, fun u v => hfinal v u⟩
  · intro ξ x y z hxy hxz hyz
    obtain ⟨η, hmove, hlong, _, hswap⟩ := exists_incomingSwap_of_covers hforward ξ z y x
      ((relationCover_dual (V := Fin n) y x).mp hxy)
      ((relationCover_dual (V := Fin n) z x).mp hxz) hyz
    refine ⟨η, hmove, (relationCover_dual (V := Fin n) z x).mpr hlong, ?_⟩
    intro u v
    simpa only [Function.swap, and_comm] using hswap v u

/-- Actual incoming flips sweep the final neighbor interval in decreasing order. -/
theorem exists_incomingSweep (hforward : Forward D) (θ : Orientation D)
    (b c d : Fin n) (hbc : b < c) (hcd : c < d) (hbd : Cover θ b d) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧ Cover η b d ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        incomingSweepRelation (D.edgeData.selected θ.val) b c d u v) := by
  obtain ⟨η, htrace, hcover, hrel⟩ := exists_incomingSweep_trace hforward θ b c d hbc hcd hbd
  exact ⟨η, outgoingSweepTrace_forget (V := OrderDual (Fin n)) _ _ d c b htrace, hcover, hrel⟩

end

end VerticalStripLLT.Circular.DiagramProof
