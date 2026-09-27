import VerticalStripLLT.Components.GainBalancedWitness

/-! Edge-instance lists retain multiplicity and endpoint balance of selected walks. -/

namespace VerticalStripLLT.Components.GainData

noncomputable section

variable {V E : Type*} (G : GainData V E)

/-- The actual edge instances of a selected walk, in traversal order. -/
def walkEdges {A : Finset E} {u v : V} (p : G.Walk A u v) : List E := by
  let : Quiver V := G.selectedQuiver A
  induction p with
  | nil => exact []
  | cons p e ih => exact ih ++ [e.val]

theorem mem_walkEdges {A : Finset E} {u v : V} (p : G.Walk A u v)
    {e : E} (he : e ∈ G.walkEdges p) : e ∈ A := by
  let : Quiver V := G.selectedQuiver A
  induction p with
  | nil => simp [walkEdges] at he
  | cons p f ih =>
    simp only [walkEdges, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact ih he
    · exact f.property.1

theorem walkGain_eq_sum_walkEdges {A : Finset E} {u v : V} (p : G.Walk A u v) :
    G.walkGain p = ((G.walkEdges p).map G.gain).sum := by
  let : Quiver V := G.selectedQuiver A
  induction p with
  | nil => simp [walkGain, walkEdges]
  | cons p e ih =>
    simp only [walkGain, Quiver.Path.addWeight_cons] at ih ⊢
    simpa [walkEdges, ih]

/-- Every walk balances its edge endpoints up to its initial and final vertices. -/
theorem walkEdges_endpoint_perm {A : Finset E} {u v : V} (p : G.Walk A u v) :
    ((G.walkEdges p).map G.head ++ [u]).Perm
      ((G.walkEdges p).map G.tail ++ [v]) := by
  let : Quiver V := G.selectedQuiver A
  induction p with
  | nil => simp [walkEdges]
  | @cons b c p e ih =>
    simp only [walkEdges, List.map_append, List.map_cons, List.map_nil,
      e.property.2.1, e.property.2.2]
    have hcomm :
        (((G.walkEdges p).map G.head ++ [c]) ++ [u]).Perm
          (((G.walkEdges p).map G.head ++ [u]) ++ [c]) := by
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := [c]) (l₂ := [u])).append_left
          ((G.walkEdges p).map G.head)
    exact hcomm.trans (ih.append_right [c])

theorem closedWalkEdges_endpoint_perm {A : Finset E} {v : V} (p : G.Walk A v v) :
    ((G.walkEdges p).map G.head).Perm ((G.walkEdges p).map G.tail) := by
  have h := G.walkEdges_endpoint_perm p
  exact (List.perm_append_right_iff [v]).mp h

end

end VerticalStripLLT.Components.GainData
