import VerticalStripLLT.Components.DiagramProof.GoodEdges

/-!
# Natural edges between two corner chains

Retained corners cannot lie properly inside natural intervals. This gives the
unique endpoint order of parallel copies before any selected-state flip is used.
-/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

include hforward

/-- At a corner head, the natural boundary is exactly its tail. -/
theorem boundary_eq_tail {e : Edge D.area} (he : e ∈ F.edges) :
    D.boundary (e.head.val : ℤ) = (e.tail.val : ℤ) := by
  have h := (D.naturalLift_of_tail_lt_head e (hforward e)).2
  rw [Diagram.boundary, Orientation.residue_intCast_eq, ← (F.corner e he).1]
  lia

/-- A natural edge ending beyond a corner cannot start strictly before that corner. -/
theorem corner_tail_le_of_head_le {e f : Edge D.area} (he : e ∈ F.edges)
    (hh : e.head ≤ f.head) : e.tail ≤ f.tail := by
  have hbound := (D.boundaryNaturalLift_of_naturalLift
    (D.naturalLift_of_tail_lt_head f (hforward f))).1
  have hmono := D.boundary_monotone (show (e.head.val : ℤ) ≤ f.head.val by exact_mod_cast hh)
  rw [F.boundary_eq_tail hforward he] at hmono
  exact_mod_cast hmono.trans hbound

/-- Every strict predecessor of an edge's head in its chain is at or before the edge's tail. -/
theorem predecessor_le_tail (e : Edge D.area) {u : Fin n}
    (hp : Relation.ReflTransGen F.step u e.head) (hne : u ≠ e.head) : u ≤ e.tail := by
  rcases hp.cases_head with heq | ⟨v, huv, hrest⟩
  · exact (hne heq).elim
  · obtain ⟨f, hf, hft, hfh⟩ := (F.step_iff u v).mp huv
    have hv := reachable_le (fun {_ _} h => F.step_forward hforward h) hrest
    have hh : f.head ≤ e.head := hfh.le.trans hv
    exact hft ▸ F.corner_tail_le_of_head_le hforward hf hh

/-- A tail has at most one natural neighbor in any other fixed corner chain. -/
theorem edge_eq_of_tail_and_head_terminal_eq (e f : Edge D.area) (ht : e.tail = f.tail)
    (hh : F.terminal hforward e.head = F.terminal hforward f.head) : e = f := by
  have hhead : e.head = f.head := by
    rcases lt_trichotomy e.head f.head with hlt | heq | hgt
    · have hp := (F.reachable_iff hforward e.head f.head).mpr ⟨hlt.le, hh⟩
      have hle := F.predecessor_le_tail hforward f hp hlt.ne
      rw [← ht] at hle
      exact (not_le_of_gt (hforward e) hle).elim
    · exact heq
    · have hp := (F.reachable_iff hforward f.head e.head).mpr ⟨hgt.le, hh.symm⟩
      have hle := F.predecessor_le_tail hforward e hp hgt.ne
      rw [ht] at hle
      exact (not_le_of_gt (hforward f) hle).elim
  exact D.endpointEmbedding.injective (Prod.ext ht hhead)

/-- A non-corner edge ends strictly before every later vertex of its tail's corner chain. -/
theorem head_lt_of_chain_reachable (e : Edge D.area) (he : e ∉ F.edges) {v : Fin n}
    (hp : Relation.ReflTransGen F.step e.tail v) (hlt : e.tail < v) : e.head < v := by
  rcases hp.cases_head with heq | ⟨w, hstep, hrest⟩
  · exact (hlt.ne heq).elim
  · obtain ⟨f, hf, hft, hfh⟩ := (F.step_iff _ _).mp hstep
    have hew : e.head ≤ w := hfh ▸ F.head_le_of_same_tail hforward hf hft.symm
    have hwv := reachable_le (fun {_ _} h => F.step_forward hforward h) hrest
    have hne : e.head ≠ w := by
      intro h
      have hfe : f = e := D.endpointEmbedding.injective (Prod.ext hft (hfh.trans h.symm))
      exact he (hfe ▸ hf)
    exact (lt_of_le_of_ne hew hne).trans_le hwv

/-- Parallel copies in increasing tail order also have separated, increasing endpoints. -/
theorem parallel_endpoints_ordered (e f : Edge D.area) (he : e ∉ F.edges)
    (ht : F.terminal hforward e.tail = F.terminal hforward f.tail)
    (hlt : e.tail < f.tail) : e.head < f.tail :=
  F.head_lt_of_chain_reachable hforward e he
    ((F.reachable_iff hforward e.tail f.tail).mpr ⟨hlt.le, ht⟩) hlt

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
