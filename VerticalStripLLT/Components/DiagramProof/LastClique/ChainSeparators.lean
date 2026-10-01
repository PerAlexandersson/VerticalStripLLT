import VerticalStripLLT.Components.DiagramProof.Corners.GoodEdgeConnectivity
import VerticalStripLLT.Components.DiagramProof.Corners.CopyGeometry
import VerticalStripLLT.Components.DiagramProof.Foundation.IntervalDeletion

/-! Deleting one corner chain leaves the other chains connected. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- Replacing natural edges by good paths stays inside any chosen set of chains. -/
theorem goodEdge_weakReach_within_terminals_iff (S : Set (Fin n)) (u v : Fin n) :
    Relation.EqvGen (fun x y => S (F.terminal hforward x) ∧
      S (F.terminal hforward y) ∧ F.goodEdgeRelation hforward x y) u v ↔
    Relation.EqvGen (fun x y => S (F.terminal hforward x) ∧
      S (F.terminal hforward y) ∧ naturalRel D x y) u v := by
  constructor
  · apply Relation.EqvGen.mono
    rintro x y ⟨hx, hy, e, _, ht, hh⟩
    exact ⟨hx, hy, e, ht, hh⟩
  · apply Relation.EqvGen.eqvGen_le
    rintro x y ⟨hx, hy, e, rfl, rfl⟩
    by_cases he : F.GoodEdge hforward e
    · exact Relation.EqvGen.rel _ _
        ⟨hx, hy, e, (F.mem_goodEdges hforward e).mpr he, rfl, rfl⟩
    · have hnot : e ∉ F.edges := fun h => he (Or.inl h)
      have hgt : F.terminal hforward e.head < F.terminal hforward e.tail := by
        rcases lt_trichotomy (F.terminal hforward e.tail)
          (F.terminal hforward e.head) with hlt | heq | hgt
        · exact (he (Or.inr hlt)).elim
        · exact (hnot ((F.terminal_eq_iff_mem hforward e).mp heq)).elim
        · exact hgt
      obtain ⟨z, hstep, hez, hterm⟩ := F.successor_of_inversion hforward e hgt
      obtain ⟨c, hc, hct, hch⟩ := (F.step_iff _ _).mp hstep
      obtain ⟨f, hft, hfh⟩ := exists_edge_of_naturalLift_of_le
        (D.naturalLift_of_tail_lt_head c (hforward c))
        (by rw [hct]; exact (hforward e).le) hez (by rw [hch])
      have hz : S (F.terminal hforward z) := by rw [hterm]; exact hx
      have hf : f ∈ F.goodEdges hforward := by
        apply (F.mem_goodEdges hforward f).mpr
        exact Or.inr (by simpa only [hft, hfh, hterm] using hgt)
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.rel _ _ ⟨hx, hz, c,
          (F.mem_goodEdges hforward c).mpr (Or.inl hc), hct, hch⟩)
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨hy, hz, f, hf, hft, hfh⟩))

/-- If all edges of length one and two are natural, consecutive vertices
belong to different corner chains. -/
theorem terminal_ne_of_consecutive (hn : 3 ≤ n)
    (hshort : ∀ u v : Fin n, u < v → v.val ≤ u.val + 2 → naturalRel D u v)
    (u v : Fin n) (huv : u.val + 1 = v.val) :
    F.terminal hforward u ≠ F.terminal hforward v := by
  intro heq
  obtain ⟨e, het, heh⟩ := hshort u v (by change u.val < v.val; lia) (by lia)
  have he : e ∈ F.edges := (F.terminal_eq_iff_mem hforward e).mp (by
    simpa only [het, heh] using heq)
  by_cases hu : u.val = 0
  · let w : Fin n := ⟨2, by lia⟩
    obtain ⟨f, hft, hfh⟩ := hshort u w (by change u.val < 2; lia) (by simp [w])
    have hh := F.head_le_of_same_tail hforward he (hft.trans het.symm)
    rw [hfh, heh] at hh
    change 2 ≤ v.val at hh
    lia
  · let w : Fin n := ⟨u.val - 1, by have := u.isLt; lia⟩
    obtain ⟨f, hft, hfh⟩ := hshort w v (by change u.val - 1 < v.val; lia)
      (by change v.val ≤ u.val - 1 + 2; lia)
    have ht := F.corner_tail_le_of_head_le hforward (f := f) he (by rw [heh, hfh])
    rw [het, hft] at ht
    change u.val ≤ u.val - 1 at ht
    lia

/-- Any two vertices outside one corner chain remain connected by good edges
outside that chain. -/
theorem goodEdge_weakReach_avoiding_terminal (hn : 3 ≤ n)
    (hshort : ∀ u v : Fin n, u < v → v.val ≤ u.val + 2 → naturalRel D u v)
    (t u v : Fin n) (hu : F.terminal hforward u ≠ t) (hv : F.terminal hforward v ≠ t) :
    Relation.EqvGen (fun x y => F.terminal hforward x ≠ t ∧
      F.terminal hforward y ≠ t ∧ F.goodEdgeRelation hforward x y) u v := by
  apply (F.goodEdge_weakReach_within_terminals_iff hforward {x | x ≠ t} u v).mpr
  apply eqvGen_of_short_edges_of_no_consecutive_omissions hshort _ u v hu hv
  intro x y hxy
  by_cases hx : F.terminal hforward x ≠ t
  · exact Or.inl hx
  · exact Or.inr (fun hy => F.terminal_ne_of_consecutive hforward hn hshort x y hxy
      ((not_not.mp hx).trans hy.symm))

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
