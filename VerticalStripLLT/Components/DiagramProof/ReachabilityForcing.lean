import VerticalStripLLT.Components.DiagramProof.HullReduction

/-! Actual flips make any ordered pair in one selected weak block comparable. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

/-- Any ordered pair in one selected weak block can be made reachable by actual flips. -/
theorem exists_reachable_of_weakReach (hforward : Forward D) (θ : Orientation D)
    (u v : Fin n) (huv : u ≤ v) (hweak : WeakReach θ u v) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      Relation.ReflTransGen (D.edgeData.selected η.val) u v := by
  cases n with
  | zero => exact Fin.elim0 u
  | succ m =>
    have hw : Relation.EqvGen
        (fun x y => (0 ≤ x ∧ x ≤ Fin.last m) ∧ (0 ≤ y ∧ y ≤ Fin.last m) ∧
          D.edgeData.selected θ.val x y) u v := by
      apply Relation.EqvGen.mono ?_ u v hweak
      intro x y hxy
      exact ⟨⟨Fin.zero_le _, Fin.le_last _⟩, ⟨Fin.zero_le _, Fin.le_last _⟩, hxy⟩
    obtain ⟨η, hθη, hη⟩ := exists_weakReach_within_endpoints hforward θ
      0 (Fin.last m) u v (Fin.zero_le _) huv (Fin.le_last _) hw
    obtain ⟨ξ, hηξ, hξ⟩ := exists_reachable_within_interval hforward η u v huv hη
    exact ⟨ξ, hθη.trans (flip_reachable_of_reverse_directed_within hηξ), hξ⟩

/-- For adjacent vertices, the reachable endpoint must select their edge. -/
theorem exists_selected_adjacent_of_weakReach (hforward : Forward D) (θ : Orientation D)
    (u v : Fin n) (hadj : v.val = u.val + 1) (hweak : WeakReach θ u v) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      D.edgeData.selected η.val u v := by
  have huv : u < v := by change u.val < v.val; lia
  obtain ⟨η, hp, hr⟩ := exists_reachable_of_weakReach hforward θ u v huv.le hweak
  refine ⟨η, hp, selected_of_cover hforward ⟨huv, hr, ?_⟩⟩
  intro w huw hwv _
  have hwlo : u.val < w.val := huw
  have hwhi : w.val < v.val := hwv
  lia

/-- An adjacent edge absent throughout a whole component has endpoints in different weak blocks. -/
theorem not_weakReach_of_adjacent_absent (hforward : Forward D) (θ : Orientation D)
    (u v : Fin n) (hadj : v.val = u.val + 1)
    (habsent : ∀ η ∈ flipComponent D θ, ¬ D.edgeData.selected η.val u v) :
    ¬ WeakReach θ u v := by
  intro hw
  obtain ⟨η, hp, hs⟩ := exists_selected_adjacent_of_weakReach hforward θ u v hadj hw
  exact habsent η (mem_flipComponent_iff.mpr hp) hs

/-- From a least weak-block vertex, reachability can be forced without losing any selected
weak connection in a retained lower interval containing both endpoints. -/
theorem exists_reachable_preserving_lower_weakReach (hforward : Forward D)
    (θ : Orientation D) (u v t : Fin n)
    (hmin : ∀ w, WeakReach θ u w → u ≤ w) (hweak : WeakReach θ u v) (hvt : v ≤ t) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      Relation.ReflTransGen (D.edgeData.selected η.val) u v ∧
      ∀ x y,
        Relation.EqvGen (fun a b => a ≤ t ∧ b ≤ t ∧ D.edgeData.selected θ.val a b) x y →
        Relation.EqvGen (fun a b => a ≤ t ∧ b ≤ t ∧ D.edgeData.selected η.val a b) x y := by
  cases n with
  | zero => exact Fin.elim0 u
  | succ m =>
    have hut : u ≤ t := (hmin v hweak).trans hvt
    have hw : Relation.EqvGen
        (fun x y => (u ≤ x ∧ x ≤ Fin.last m) ∧ (u ≤ y ∧ y ≤ Fin.last m) ∧
          D.edgeData.selected θ.val x y) u v :=
      eqvGen_within_of_class_subset _ hweak (fun w hw => ⟨hmin w hw, Fin.le_last _⟩)
    obtain ⟨η, hθη, hη, hkeep⟩ := exists_weakReach_with_smaller_upper_bound hforward
      θ u (Fin.last m) t u v le_rfl hut hvt (Fin.le_last _) hw
    let S : Set (Fin (m + 1)) := {x | u ≤ x ∧ x ≤ t}
    have hminη (w : Fin (m + 1))
        (hw : Relation.EqvGen
          (fun a b => S a ∧ S b ∧ D.edgeData.selected η.val a b) u w) : u ≤ w := by
      have hweakη : WeakReach η u w :=
        Relation.EqvGen.mono (fun _ _ h => h.2.2) _ _ hw
      exact hmin w ((weakReach_iff_of_reachable hθη u w).mpr hweakη)
    obtain ⟨ξ, hηξ, hξ⟩ := exists_reachable_within_of_minimal hforward S
      (fun _ _ _ hx hy hxz hzy => ⟨hx.1.trans hxz, hzy.trans hy.2⟩) η u v hminη hη
    refine ⟨ξ, hθη.trans (flip_reachable_of_reverse_directed_within hηξ), hξ, ?_⟩
    intro x y hxy
    have hxyη : Relation.EqvGen
        (fun a b => a ≤ t ∧ b ≤ t ∧ D.edgeData.selected η.val a b) x y := by
      apply Relation.EqvGen.mono ?_ x y hxy
      intro a b h
      exact ⟨h.1, h.2.1, hkeep a b h.2.1 h.2.2⟩
    exact (weakReach_within_iff_of_reverse_directed_reachable
      (T := {a | a ≤ t}) (fun _ hx => hx.2) hηξ x y).mp hxyη

end VerticalStripLLT.Circular.DiagramProof
