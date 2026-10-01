import VerticalStripLLT.Components.DiagramProof.Preparation.ReachabilityForcing

/-! Connecting the lower part of one weak block by actual flips. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

/-- A forward path ending below the cutoff gives a weak path below that cutoff. -/
theorem lower_weakReach_of_reachable (hD : Forward D) (θ : Orientation D)
    (t : Fin n) {u v : Fin n}
    (hp : Relation.ReflTransGen (D.edgeData.selected θ.val) u v) (hvt : v ≤ t) :
    Relation.EqvGen (fun a b => a ≤ t ∧ b ≤ t ∧ D.edgeData.selected θ.val a b) u v := by
  induction hp with
  | refl => exact Relation.EqvGen.refl _
  | @tail x y hux hxy ih =>
    have hxt : x ≤ t := (θ.selected_lt_of_forward hD hxy).le.trans hvt
    exact Relation.EqvGen.trans _ _ _ (ih hxt)
      (Relation.EqvGen.rel _ _ ⟨hxt, hvt, hxy⟩)

/-- Connect any finite list of lower vertices to the least vertex of its weak block,
while preserving every lower weak connection already present. -/
theorem exists_lower_connections_finset (hD : Forward D) (θ : Orientation D)
    (u t : Fin n) (hmin : ∀ w, WeakReach θ u w → u ≤ w)
    (s : Finset (Fin n)) (hs : ∀ v ∈ s, WeakReach θ u v ∧ v ≤ t) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      (∀ v ∈ s, Relation.EqvGen
        (fun a b => a ≤ t ∧ b ≤ t ∧ D.edgeData.selected η.val a b) u v) ∧
      ∀ x y, Relation.EqvGen
        (fun a b => a ≤ t ∧ b ≤ t ∧ D.edgeData.selected θ.val a b) x y →
        Relation.EqvGen
          (fun a b => a ≤ t ∧ b ≤ t ∧ D.edgeData.selected η.val a b) x y := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨θ, .refl, by simp, fun _ _ h => h⟩
  | @insert v s hv ih =>
    obtain ⟨η, hp, hη, hkeepη⟩ := ih (fun w hw => hs w (Finset.mem_insert_of_mem hw))
    have hvθ := hs v (Finset.mem_insert_self _ _)
    have hminη (w : Fin n) (hw : WeakReach η u w) : u ≤ w :=
      hmin w ((weakReach_iff_of_reachable hp u w).mpr hw)
    obtain ⟨ζ, hηζ, hvζ, hkeepζ⟩ := exists_reachable_preserving_lower_weakReach
      hD η u v t hminη ((weakReach_iff_of_reachable hp u v).mp hvθ.1) hvθ.2
    refine ⟨ζ, hp.trans hηζ, ?_, fun x y h => hkeepζ x y (hkeepη x y h)⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact lower_weakReach_of_reachable hD ζ t hvζ hvθ.2
    · exact hkeepζ u w (hη w hw)

/-- The retained lower vertices of a weak block can all be connected below the cutoff. -/
theorem exists_connected_lower_part (hD : Forward D) (θ : Orientation D)
    (u t : Fin n) (hmin : ∀ w, WeakReach θ u w → u ≤ w) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      (∀ v, WeakReach θ u v → v ≤ t → Relation.EqvGen
        (fun a b => a ≤ t ∧ b ≤ t ∧ D.edgeData.selected η.val a b) u v) ∧
      ∀ x y, Relation.EqvGen
        (fun a b => a ≤ t ∧ b ≤ t ∧ D.edgeData.selected θ.val a b) x y →
        Relation.EqvGen
          (fun a b => a ≤ t ∧ b ≤ t ∧ D.edgeData.selected η.val a b) x y := by
  classical
  obtain ⟨η, hp, hη, hkeep⟩ := exists_lower_connections_finset hD θ u t hmin
    (Finset.univ.filter fun v => WeakReach θ u v ∧ v ≤ t)
    (fun _ hv => (Finset.mem_filter.mp hv).2)
  exact ⟨η, hp, fun v hv hvt => hη v (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hv, hvt⟩), hkeep⟩

end VerticalStripLLT.Circular.DiagramProof
