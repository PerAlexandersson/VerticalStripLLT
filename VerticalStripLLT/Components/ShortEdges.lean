import VerticalStripLLT.Circular.StrictCornerAdjacency

/-! Natural short edges and forward orientations for the component flip bijection. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

variable {n : ℕ} (D : Diagram n)

/-- Every selected edge set is acyclic when all natural edges point forward. -/
theorem admissible_of_forward (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (A : Finset (Edge D.area)) : D.edgeData.Admissible A := by
  intro v hcycle
  exact (lt_irrefl v)
    (D.edgeData.lt_of_transGen A id (fun e _ => hforward e) hcycle)

/-- A subset of normal edges gives an actual orientation in the forward case. -/
def orientationOfForward (hforward : ∀ e : Edge D.area, e.tail < e.head)
    (A : Finset (Edge D.area)) (hA : A ⊆ D.edgeData.normalEdges) : Orientation D :=
  ⟨A, hA, D.admissible_of_forward hforward A⟩

/-- A forward edge has its natural lift at the canonical integer representatives. -/
theorem naturalLift_of_tail_lt_head (e : Edge D.area) (he : e.tail < e.head) :
    D.naturalLift e (e.tail.val : ℤ) (e.head.val : ℤ) := by
  have hm := e.tail_add_length_mod
  have ht := e.tail.isLt
  have hl := e.length_lt_n
  have hforward : e.tail.val < e.head.val := he
  have hsum : e.tail.val + e.length.val < n := by
    by_contra h
    have hge : n ≤ e.tail.val + e.length.val := by lia
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by lia)] at hm
    lia
  rw [Nat.mod_eq_of_lt hsum] at hm
  refine ⟨Orientation.residue_intCast_eq e.tail, ?_⟩
  exact_mod_cast hm.symm

/-- The specified lift of a natural edge is a boundary interval. -/
theorem boundaryNaturalLift_of_naturalLift {e : Edge D.area} {a c : ℤ}
    (hac : D.naturalLift e a c) : D.boundaryNaturalLift a c := by
  apply D.boundaryNaturalLift_of_edge
  · rw [hac.2]
    exact (D.residue_add_length e a hac.1).symm
  · have h := hac.2
    lia

/-- Both proper short edges of a natural lifted interval exist and are normal. -/
theorem normalShortEdges_of_boundaryNaturalLift {a b c : ℤ}
    (hac : D.boundaryNaturalLift a c) (hab : a < b) (hbc : b < c) :
    ∃ eab ebc : Edge D.area,
      eab ∈ D.edgeData.normalEdges ∧ ebc ∈ D.edgeData.normalEdges ∧
        D.naturalLift eab a b ∧ D.naturalLift ebc b c := by
  have hab' : D.boundaryNaturalLift a b :=
    ⟨(D.boundary_monotone hbc.le).trans hac.1, hab⟩
  have hbc' : D.boundaryNaturalLift b c := ⟨hac.1.trans hab.le, hbc⟩
  refine ⟨D.edgeFromLift a b hab', D.edgeFromLift b c hbc', ?_, ?_,
    D.edgeFromLift_naturalLift hab', D.edgeFromLift_naturalLift hbc'⟩
  · apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hs
    have hlen := D.length_le_of_strict_same_tail hs
      (show (D.edgeFromLift a c hac).tail = (D.edgeFromLift a b hab').tail by
        rw [D.edgeFromLift_tail, D.edgeFromLift_tail])
    have hlen' : ((D.edgeFromLift a c hac).length.val : ℤ) ≤
        (D.edgeFromLift a b hab').length.val := by exact_mod_cast hlen
    rw [D.edgeFromLift_length, D.edgeFromLift_length] at hlen'
    lia
  · apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hs
    have hb := ((D.edgeFromLift_mem_strict_iff hbc').mp hs).2
    have ha := hac.1
    lia

/-- The short-edge construction applied directly to a specified lifted long edge. -/
theorem normalShortEdges_of_naturalLift {e : Edge D.area} {a b c : ℤ}
    (hac : D.naturalLift e a c) (hab : a < b) (hbc : b < c) :
    ∃ eab ebc : Edge D.area,
      eab ∈ D.edgeData.normalEdges ∧ ebc ∈ D.edgeData.normalEdges ∧
        D.naturalLift eab a b ∧ D.naturalLift ebc b c :=
  D.normalShortEdges_of_boundaryNaturalLift
    (D.boundaryNaturalLift_of_naturalLift hac) hab hbc

end VerticalStripLLT.Circular.Diagram
