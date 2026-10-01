import VerticalStripLLT.Components.DiagramProof.Corners.GoodEdgeConnectivity
import VerticalStripLLT.Components.DiagramProof.Corners.CliqueEdges
import VerticalStripLLT.Components.DiagramProof.Foundation.IntervalDeletion

/-! Connectivity after deleting a vertex forces the short natural edges. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

namespace CornerFamily

variable {n : ℕ} {D : Diagram n}

theorem naturalRel_of_le_of_le (hforward : Forward D) {x y a b : Fin n}
    (hxy : naturalRel D x y) (hxa : x ≤ a) (hab : a < b)
    (hby : b ≤ y) : naturalRel D a b := by
  obtain ⟨e, ht, hh⟩ := hxy
  obtain ⟨f, hft, hfh⟩ := exists_edge_of_naturalLift_of_le
    (D.naturalLift_of_tail_lt_head e (hforward e))
    (by simpa only [ht] using hxa) hab (by simpa only [hh] using hby)
  exact ⟨f, hft, hfh⟩

/-- A weak path outside an open interval forces its endpoint edge to be natural. -/
theorem naturalRel_of_eqvGen_of_side
    (hforward : Forward D) {R : Fin n → Fin n → Prop} {a b : Fin n} (hab : a < b)
    (hR : ∀ ⦃x y⦄, R x y → naturalRel D x y)
    (hside : ∀ ⦃x y⦄, R x y →
      (x ≤ a ∨ b ≤ x) ∧ (y ≤ a ∨ b ≤ y))
    (hpath : Relation.EqvGen R a b) : naturalRel D a b := by
  by_contra habN
  have hstable : ∀ ⦃x y⦄, R x y → (x ≤ a ↔ y ≤ a) := by
    intro x y hxy
    obtain ⟨hxs, hys⟩ := hside hxy
    constructor
    · intro hx
      by_contra hnoty
      rcases hys with hy | hy
      · exact hnoty hy
      · exact habN (naturalRel_of_le_of_le hforward (hR hxy) hx hab hy)
    · intro hy
      by_contra hnotx
      rcases hxs with hx | hx
      · exact hnotx hx
      · have hlt := naturalRel_forward hforward (hR hxy)
        have hba : b < a := hx.trans_lt (hlt.trans_le hy)
        exact (not_lt_of_ge hab.le) hba
  have hstableEqv : ∀ ⦃x y⦄, Relation.EqvGen R x y → (x ≤ a ↔ y ≤ a) := by
    intro x y hxy
    induction hxy with
    | rel x y hxy => exact hstable hxy
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hba : b ≤ a := (hstableEqv hpath).mp le_rfl
  exact (not_le_of_gt hab) hba

private theorem le_or_ge_of_adjacent {u v x : Fin n}
    (hval : v.val = u.val + 1) : x ≤ u ∨ v ≤ x := by
  by_cases hxu : x ≤ u
  · exact Or.inl hxu
  · right
    have hux := lt_of_not_ge hxu
    change u.val < x.val at hux
    change v.val ≤ x.val
    rw [hval]
    lia

private theorem le_or_ge_of_distance_two {u v w x : Fin n} (huw : w.val = u.val + 1)
    (huv : v.val = u.val + 2) (hxw : x ≠ w) : x ≤ u ∨ v ≤ x := by
  by_cases hxu : x ≤ u
  · exact Or.inl hxu
  · right
    have hux := lt_of_not_ge hxu
    change u.val < x.val at hux
    have hxwval : x.val ≠ u.val + 1 := by
      intro h
      apply hxw
      apply Fin.ext
      rw [huw]
      exact h
    change v.val ≤ x.val
    rw [huv]
    lia

/-- A connected natural diagram which remains connected after deleting every vertex has all
length-one and length-two natural edges. -/
theorem naturalRel_short_of_connected_of_delete
    (hforward : Forward D)
    (hconn : ∀ u v, Relation.EqvGen (naturalRel D) u v)
    (hdelete : ∀ w u v, u ≠ w → v ≠ w →
      Relation.EqvGen (fun x y => x ≠ w ∧ y ≠ w ∧
        naturalRel D x y) u v) :
    ∀ u v, u < v → v.val ≤ u.val + 2 → naturalRel D u v := by
  intro u v huv hgap
  have hlow : u.val + 1 ≤ v.val := by
    have huvval : u.val < v.val := huv
    lia
  have hcases : v.val = u.val + 1 ∨ v.val = u.val + 2 := by
    rcases Nat.eq_or_lt_of_le hlow with h | h
    · exact Or.inl h.symm
    · right
      lia
  rcases hcases with hval | hval
  · apply naturalRel_of_eqvGen_of_side hforward huv
      (fun {_ _} h => h)
    · intro x y _
      exact ⟨le_or_ge_of_adjacent hval, le_or_ge_of_adjacent hval⟩
    · exact hconn u v
  · let w : Fin n := ⟨u.val + 1, by
      have hv := v.isLt
      rw [hval] at hv
      lia⟩
    have hwu : u ≠ w := by
      intro h
      have hval' := congrArg Fin.val h
      change u.val = u.val + 1 at hval'
      lia
    have hvw : v ≠ w := by
      intro h
      have hval' := congrArg Fin.val h
      change v.val = u.val + 1 at hval'
      rw [hval] at hval'
      lia
    apply naturalRel_of_eqvGen_of_side hforward
      (R := fun x y => x ≠ w ∧ y ≠ w ∧ naturalRel D x y) huv
      (fun {_ _} h => h.2.2)
    · intro x y hxy
      exact ⟨le_or_ge_of_distance_two (rfl : w.val = u.val + 1) hval hxy.1,
        le_or_ge_of_distance_two (rfl : w.val = u.val + 1) hval hxy.2.1⟩
    · exact hdelete w u v hwu hvw

/-- Short natural edges connect every pair of vertices. -/
theorem naturalRel_connected_of_short
    (hshort : ∀ u v : Fin n, u < v → v.val ≤ u.val + 2 → naturalRel D u v)
    (u v : Fin n) : Relation.EqvGen (naturalRel D) u v := by
  have hp := eqvGen_of_short_edges_of_no_consecutive_omissions
    (S := Set.univ) hshort (fun _ _ _ => Or.inl trivial) u v trivial trivial
  exact Relation.EqvGen.mono (fun _ _ h => h.2.2) _ _ hp

/-- Short natural edges also connect all surviving vertices after any one vertex is deleted. -/
theorem naturalRel_delete_of_short
    (hshort : ∀ u v : Fin n, u < v → v.val ≤ u.val + 2 → naturalRel D u v)
    (w u v : Fin n) (hu : u ≠ w) (hv : v ≠ w) :
    Relation.EqvGen (fun x y => x ≠ w ∧ y ≠ w ∧ naturalRel D x y) u v := by
  apply eqvGen_of_short_edges_of_no_consecutive_omissions hshort _ u v hu hv
  intro x y hxy
  by_cases hx : x = w
  · right
    intro hy
    have heq := congrArg Fin.val (hx.trans hy.symm)
    lia
  · exact Or.inl hx

end CornerFamily

end

end VerticalStripLLT.Circular.DiagramProof
