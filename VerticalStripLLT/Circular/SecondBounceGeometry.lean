import VerticalStripLLT.Circular.CornerBoundary
import VerticalStripLLT.Circular.DNNormalPairs
import VerticalStripLLT.Circular.SecondBounceColoring
import VerticalStripLLT.Circular.FirstBounceStrictSwap
import VerticalStripLLT.Circular.PairBackground

/-! The actual circular DN coloring recurrence, with exterior geometry discharged. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

theorem coloringLLT_dnSuccessor
    (e f : Edge D.area) (he : e ∈ D.strict) (hf : f ∈ D.strict) (hne : f ≠ e)
    (hcontact : f.tail = e.head)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
    (hlen : 2 ≤ f.length.val)
    (hgap : D.area.area (D.area.next f.head) < D.area.area f.head) (m : ℕ) :
    D.coloringLLT m = (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).coloringLLT m := by
  let R := D.deleteCorner e (D.strict_corner e he)
  let g : Edge R.area := D.cornerRestrict e (D.strict_corner e he) f hne
  have ghead : g.head = f.head := rfl
  have gtail : g.tail = f.tail := rfl
  have hg : g ∈ R.strict := (D.mem_deleteCorner_strict e (D.strict_corner e he) g).mpr hf
  have hggap : R.area.area (R.area.next g.head) < R.area.area g.head :=
    D.deleteStrictCorner_surviving_gap e f he hf hne hgap
  have hsame : R.boundary ((g.tail.val : ℤ) + 1) = R.boundary (g.tail.val : ℤ) :=
    D.dn_deleted_boundary_same e f he hcontact hlen heq
  have hr : R.residue (g.tail.val : ℤ) = e.head :=
    (Orientation.residue_intCast_eq f.tail).trans hcontact
  have hr1 : R.residue ((g.tail.val : ℤ) + 1) = D.area.next f.tail := by
    rw [R.residue_succ, R.nn_residue_P g]
    rfl
  have hleft : ¬ R.strictAt (g.tail.val : ℤ) :=
    D.deleteStrictCorner_not_strictAt e he _ hr
  have hright : ¬ R.strictAt ((g.tail.val : ℤ) + 1) := by
    apply D.deleteCorner_not_strictAt e (D.strict_corner e he)
    rintro ⟨a, ha, hh⟩
    exact hns a ha (hh.trans (hr1.trans (congrArg D.area.next hcontact)))
  have hn : 2 ≤ n := by have := f.length_lt_n; lia
  have hno : ∀ z k : ℤ, R.boundary z ≠ (g.tail.val : ℤ) + 1 + n * k := by
    intro z k h
    apply R.nn_boundary_ne g hg hggap (z + n * (-k))
    rw [R.boundary_add_period, h]
    ring
  have hs := R.firstBounce_strict_exterior_swap hg (g.tail.val : ℤ)
    (R.nn_residue_P g).symm hleft hright hno
  have hS : R.pairGraph.strictEdges = D.pairGraph.strictEdges.erase (e.tail, e.head) :=
    D.deleteCorner_pairGraph_strictEdges e (D.strict_corner e he)
  have hN : R.pairGraph.normalEdges = D.pairGraph.normalEdges :=
    D.deleteStrictCorner_pairGraph_normalEdges e he
  have hstrict : (D.secondBounceBackground e f).strictEdges.map
      (swapVertexPair e.head (D.area.next f.tail)) =
        (D.secondBounceBackground e f).strictEdges := by
    have hsc := hs
    rw [hS, hr, hr1] at hsc
    simpa only [secondBounceBackground, ghead, gtail] using hsc
  have hnat := R.naturalPairs_erase_map_swap hn (g.tail.val : ℤ) hsame hno
  have hgp : (g.tail, g.head) ∈ R.pairGraph.strictEdges :=
    (R.mem_pairGraph_strict_iff _).mpr ⟨g, hg, rfl⟩
  have hzi : f.head ≠ e.head := fun h => hne (D.strict_edge_eq_of_head_eq hf he h)
  have hzy : f.head ≠ D.area.next f.tail := by
    rw [hcontact]
    exact hns f hf
  have hnorm := normal_background_swap R.naturalPairs R.pairGraph.strictEdges
    (R.residue (g.tail.val : ℤ)) (R.residue ((g.tail.val : ℤ) + 1)) g.head
    (by simpa only [R.nn_residue_P g] using hgp)
    (by simpa only [hr, ghead] using hzi) (by simpa only [hr1, ghead] using hzy) hnat
    (by simpa only [R.nn_residue_P g] using hs)
  have hnormal : ((D.secondBounceBackground e f).normalEdges.erase
      (e.head, D.area.next f.tail)).map (swapVertexPair e.head (D.area.next f.tail)) =
        (D.secondBounceBackground e f).normalEdges.erase (e.head, D.area.next f.tail) := by
    rw [← R.normalPairs_eq_sdiff, hN, hr, hr1] at hnorm
    exact hnorm
  have hshort : (D.area.next f.tail, f.head) ∈ D.pairGraph.normalEdges := by
    apply (D.mem_pairGraph_normal_iff _).mpr
    refine ⟨D.shortenedOldEdge f hf hlen, ?_, ?_⟩
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        D.shortened_old_edge_not_strict f hf hlen⟩
    · rw [D.shortenedOldEdge_tail]
      rfl
  have hfresh : (e.tail, e.head) ∉ D.pairGraph.normalEdges := by
    rintro h
    obtain ⟨a, ha, hp⟩ := (D.mem_pairGraph_normal_iff _).mp h
    have hae : a = e := D.endpointEmbedding.injective hp
    subst a
    exact (Finset.mem_sdiff.mp ha).2 he
  have hbridge : (e.head, D.area.next f.tail) ∈
      (D.secondBounceBackground e f).normalEdges := by
    have hnbridge : (R.bridgeEdge g) ∈ R.edgeData.normalEdges := by
      rw [R.mem_normalEdges_iff]
      exact R.nn_bridge_not_strict g hsame hright
    have hpbridge : ((R.bridgeEdge g).tail, (R.bridgeEdge g).head) =
        (e.head, D.area.next f.tail) := by
      rw [R.nn_bridge_tail g hsame, R.nn_bridge_head g hsame, hr, hr1]
    have hnB : (e.head, D.area.next f.tail) ∈ D.pairGraph.normalEdges := by
      rw [← hN]
      exact (R.mem_pairGraph_normal_iff _).mpr ⟨_, hnbridge, hpbridge⟩
    exact Finset.mem_erase.mpr ⟨fun h => hzy (congrArg Prod.snd h).symm, hnB⟩
  have hay : e.tail ≠ D.area.next f.tail := by
    rw [hcontact]
    have hh := (D.raisedEdge e he heq hb).tail_ne_head
    rwa [D.raisedEdge_tail, D.raisedEdge_head] at hh
  apply D.coloringLLT_dnSuccessor_of_pair_data e f he hf hne hcontact heq hb hns hlen hgap
    (m := m)
  · exact (Finset.insert_erase hshort).symm
  · exact D.dnSuccessor_pairGraph_normalEdges e f he hf hne heq hb hns hlen hgap
  · exact Finset.notMem_erase _ _
  · exact fun h => hfresh (Finset.mem_erase.mp h).2
  · exact hbridge
  · exact hstrict
  · exact hnormal
  · exact e.tail_ne_head
  · exact hay
  · exact hzi
  · exact hzy

/-- The same direct DN identity after substituting q+1 for q. -/
theorem xQShift_coloringLLT_dnSuccessor
    (e f : Edge D.area) (he : e ∈ D.strict) (hf : f ∈ D.strict) (hne : f ≠ e)
    (hcontact : f.tail = e.head)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
    (hlen : 2 ≤ f.length.val)
    (hgap : D.area.area (D.area.next f.head) < D.area.area f.head) (m : ℕ) :
    xQShift m (D.coloringLLT m) =
      xQShift m ((D.dnSuccessor e f he hf hne heq hb hns hlen hgap).coloringLLT m) := by
  rw [D.coloringLLT_dnSuccessor e f he hf hne hcontact heq hb hns hlen hgap m]

end VerticalStripLLT.Circular.Diagram
