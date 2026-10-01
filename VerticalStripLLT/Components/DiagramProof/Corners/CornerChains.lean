import VerticalStripLLT.Components.DiagramProof.Foundation.PathTransport
import VerticalStripLLT.Components.DiagramProof.Relations.RelationPaths
import VerticalStripLLT.Circular.StrictFibers

/-!
# Corner chains and their terminal vertices

A family may contain all maximal corners or just the retained corners needed by
a preparation step. We use the existing empty-normal orientation of the diagram
marked by this family; its HRV map gives the chain terminals.
-/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

/-- Retained natural corners, including every original strict edge. -/
structure CornerFamily (D : Diagram n) where
  edges : Finset (Edge D.area)
  corner : ∀ e ∈ edges, IsCorner e
  contains_strict : D.strict ⊆ edges

/-- The full family of maximal natural corners. -/
def allCorners (D : Diagram n) : CornerFamily D where
  edges := Finset.univ.filter IsCorner
  corner := by intro e he; exact (Finset.mem_filter.mp he).2
  contains_strict := by intro e he; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    D.strict_corner e he⟩

namespace CornerFamily

variable (F : CornerFamily D)

/-- Mark exactly the retained corner family on the unchanged natural diagram. -/
def diagram : Diagram n := { D with strict := F.edges, strict_corner := F.corner }

/-- The chain edges, independently of any selected normal edges. -/
def step : Fin n → Fin n → Prop := F.diagram.edgeData.selected ∅

theorem step_iff (u v : Fin n) :
    F.step u v ↔ ∃ e ∈ F.edges, e.tail = u ∧ e.head = v := by
  change (∃ e ∈ F.edges ∪ ∅, e.tail = u ∧ e.head = v) ↔ _
  rw [Finset.union_empty]

/-- The orientation consisting of just the retained corners. -/
def chains (hforward : Forward D) : Orientation F.diagram :=
  F.diagram.orientationOfForward hforward ∅ (Finset.empty_subset _)

@[simp] theorem chains_val (hforward : Forward D) : (F.chains hforward).val = ∅ := rfl

/-- Greatest vertex of the corner chain containing `v`, including singleton chains. -/
def terminal (hforward : Forward D) : Fin n → Fin n := (F.chains hforward).hrv

theorem step_forward (hforward : Forward D) {u v : Fin n} (h : F.step u v) : u < v := by
  obtain ⟨e, _, rfl, rfl⟩ := (F.step_iff u v).mp h
  exact hforward e

theorem step_rightUnique : Relator.RightUnique F.step := F.diagram.strict_selected_rightUnique

theorem step_leftUnique : Relator.LeftUnique F.step := F.diagram.strict_selected_leftUnique

theorem reachable_terminal (hforward : Forward D) (v : Fin n) :
    Relation.ReflTransGen F.step v (F.terminal hforward v) :=
  (F.chains hforward).hrv_reachable v

theorem le_terminal (hforward : Forward D) (v : Fin n) : v ≤ F.terminal hforward v :=
  reachable_le (fun {_ _} h => F.step_forward hforward h) (F.reachable_terminal hforward v)

theorem terminal_sink (hforward : Forward D) (v w : Fin n) :
    ¬ F.step (F.terminal hforward v) w := (F.chains hforward).hrv_is_sink v w

theorem terminal_eq_of_step (hforward : Forward D) {u v : Fin n} (h : F.step u v) :
    F.terminal hforward u = F.terminal hforward v :=
  (F.chains hforward).hrv_eq_of_selected_of_empty rfl h

theorem terminal_eq_of_reachable (hforward : Forward D) {u v : Fin n}
    (h : Relation.ReflTransGen F.step u v) :
    F.terminal hforward u = F.terminal hforward v :=
  (F.chains hforward).hrv_eq_of_reachable_of_empty rfl h

@[simp] theorem terminal_idempotent (hforward : Forward D) (v : Fin n) :
    F.terminal hforward (F.terminal hforward v) = F.terminal hforward v :=
  (F.terminal_eq_of_reachable hforward (F.reachable_terminal hforward v)).symm

/-- A chain is exactly its terminal fibre, in increasing vertex order. -/
theorem reachable_iff (hforward : Forward D) (u v : Fin n) :
    Relation.ReflTransGen F.step u v ↔
      u ≤ v ∧ F.terminal hforward u = F.terminal hforward v := by
  constructor
  · intro h
    exact ⟨reachable_le (fun {_ _} h => F.step_forward hforward h) h,
      F.terminal_eq_of_reachable hforward h⟩
  · rintro ⟨huv, heq⟩
    rcases (F.chains hforward).same_hrv_comparable_of_empty rfl heq with h | h
    · exact h
    · have hEq : u = v :=
        le_antisymm huv (reachable_le (fun {_ _} h => F.step_forward hforward h) h)
      subst v
      exact Relation.ReflTransGen.refl

/-- A nonterminal vertex has its unique strict successor. -/
theorem exists_successor (hforward : Forward D) {v : Fin n}
    (hnot : v ≠ F.terminal hforward v) : ∃ w, F.step v w := by
  rcases (F.reachable_terminal hforward v).cases_head with h | ⟨w, hw, _⟩
  · exact (hnot h).elim
  · exact ⟨w, hw⟩

/-- No natural edge from a corner tail extends beyond its corner head. -/
theorem head_le_of_same_tail (hforward : Forward D) {e f : Edge D.area}
    (he : e ∈ F.edges) (ht : f.tail = e.tail) : f.head ≤ e.head := by
  have hlen := F.diagram.length_le_of_strict_same_tail he ht
  have hf := (D.naturalLift_of_tail_lt_head f (hforward f)).2
  have he' := (D.naturalLift_of_tail_lt_head e (hforward e)).2
  rw [ht] at hf
  have hlen' : (f.length.val : ℤ) ≤ e.length.val := by exact_mod_cast hlen
  have h : (f.head.val : ℤ) ≤ e.head.val := by lia
  exact_mod_cast h

/-- A natural edge inside one corner chain must itself be a retained corner. -/
theorem mem_of_terminal_eq (hforward : Forward D) (e : Edge D.area)
    (heq : F.terminal hforward e.tail = F.terminal hforward e.head) : e ∈ F.edges := by
  have hp := (F.reachable_iff hforward e.tail e.head).mpr ⟨(hforward e).le, heq⟩
  rcases hp.cases_head with h | ⟨w, hstep, hrest⟩
  · exact ((hforward e).ne h).elim
  · obtain ⟨f, hf, hft, hfh⟩ := (F.step_iff _ _).mp hstep
    have hle : e.head ≤ w := hfh ▸ F.head_le_of_same_tail hforward hf hft.symm
    have hge : w ≤ e.head := reachable_le (fun {_ _} h => F.step_forward hforward h) hrest
    have hfe : f = e := D.endpointEmbedding.injective
      (Prod.ext hft (hfh.trans (le_antisymm hge hle)))
    exact hfe ▸ hf

theorem terminal_eq_iff_mem (hforward : Forward D) (e : Edge D.area) :
    F.terminal hforward e.tail = F.terminal hforward e.head ↔ e ∈ F.edges := by
  refine ⟨F.mem_of_terminal_eq hforward e, ?_⟩
  intro he
  exact F.terminal_eq_of_step hforward ((F.step_iff _ _).mpr ⟨e, he, rfl, rfl⟩)

/-- Successive retained corners in one chain have disjoint open intervals. -/
theorem step_intervals (hforward : Forward D) {a b c d : Fin n}
    (hab : F.step a b) (hcd : F.step c d)
    (heq : F.terminal hforward a = F.terminal hforward c) :
    b ≤ c ∨ d ≤ a ∨ (a = c ∧ b = d) := by
  rcases lt_trichotomy a c with hac | rfl | hca
  · have hp := (F.reachable_iff hforward a c).mpr ⟨hac.le, heq⟩
    rcases hp.cases_head with h | ⟨w, hw, hrest⟩
    · exact (hac.ne h).elim
    · have hwEq : w = b := F.step_rightUnique hw hab
      subst w
      exact Or.inl (reachable_le (fun {_ _} h => F.step_forward hforward h) hrest)
  · exact Or.inr (Or.inr ⟨rfl, F.step_rightUnique hab hcd⟩)
  · have hp := (F.reachable_iff hforward c a).mpr ⟨hca.le, heq.symm⟩
    rcases hp.cases_head with h | ⟨w, hw, hrest⟩
    · exact (hca.ne h).elim
    · have hwEq : w = d := F.step_rightUnique hw hcd
      subst w
      exact Or.inr (Or.inl
        (reachable_le (fun {_ _} h => F.step_forward hforward h) hrest))

/-- An edge decreasing the chain terminal lies strictly inside its tail's next corner. -/
theorem successor_of_inversion (hforward : Forward D) (e : Edge D.area)
    (hinv : F.terminal hforward e.head < F.terminal hforward e.tail) :
    ∃ h, F.step e.tail h ∧ e.head < h ∧
      F.terminal hforward h = F.terminal hforward e.tail := by
  have hyt := (F.le_terminal hforward e.head).trans_lt hinv
  have hvt := (hforward e).trans hyt
  obtain ⟨h, hstep⟩ := F.exists_successor hforward hvt.ne
  obtain ⟨f, hf, hft, hfh⟩ := (F.step_iff _ _).mp hstep
  have hyh : e.head ≤ h := hfh ▸ F.head_le_of_same_tail hforward hf hft.symm
  have hterm := F.terminal_eq_of_step hforward hstep
  have hne : e.head ≠ h := by
    intro heq
    rw [heq, ← hterm] at hinv
    exact lt_irrefl _ hinv
  exact ⟨h, hstep, lt_of_le_of_ne hyh hne, hterm.symm⟩

end CornerFamily

end

end VerticalStripLLT.Circular.DiagramProof
