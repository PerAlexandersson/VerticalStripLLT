import VerticalStripLLT.Components.DiagramProof.Preparation.PathShortening

/-! Repeated extreme-vertex removal puts a selected weak path inside its endpoint interval. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

/-- Lower the upper bound of a weak path while retaining every selected edge below the new bound. -/
theorem exists_weakReach_with_smaller_upper_bound (hforward : Forward D)
    (θ : Orientation D) (a b c u v : Fin n)
    (hau : a ≤ u) (huc : u ≤ c) (hvc : v ≤ c) (hcb : c ≤ b)
    (hweak : Relation.EqvGen
      (fun x y => (a ≤ x ∧ x ≤ b) ∧ (a ≤ y ∧ y ≤ b) ∧
        D.edgeData.selected θ.val x y) u v) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      Relation.EqvGen
        (fun x y => (a ≤ x ∧ x ≤ c) ∧ (a ≤ y ∧ y ≤ c) ∧
          D.edgeData.selected η.val x y) u v ∧
      ∀ x y, y ≤ c → D.edgeData.selected θ.val x y → D.edgeData.selected η.val x y := by
  suffices aux : ∀ N, ∀ (θ : Orientation D) (b : Fin n), b.val = N → c ≤ b →
      Relation.EqvGen
        (fun x y => (a ≤ x ∧ x ≤ b) ∧ (a ≤ y ∧ y ≤ b) ∧
          D.edgeData.selected θ.val x y) u v →
      ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
        Relation.EqvGen
          (fun x y => (a ≤ x ∧ x ≤ c) ∧ (a ≤ y ∧ y ≤ c) ∧
            D.edgeData.selected η.val x y) u v ∧
        ∀ x y, y ≤ c → D.edgeData.selected θ.val x y → D.edgeData.selected η.val x y by
    exact aux b.val θ b rfl hcb hweak
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro θ b hN hcb hweak
    by_cases heq : b = c
    · subst b
      exact ⟨θ, Relation.ReflTransGen.refl, hweak, fun _ _ _ h => h⟩
    have hcb' : c < b := lt_of_le_of_ne hcb (Ne.symm heq)
    obtain ⟨η, hθη, hη, hkeep⟩ := exists_weakReach_below hforward θ a b u v hau
      (huc.trans_lt hcb') (hvc.trans_lt hcb') hweak
    let b' : Fin n := ⟨b.val - 1, (Nat.sub_le b.val 1).trans_lt b.isLt⟩
    have hcb'' : c ≤ b' := by change c.val ≤ b.val - 1; exact Nat.le_sub_one_of_lt hcb'
    have hlt : b'.val < N := by
      change b.val - 1 < N
      have hpos : 0 < b.val := Nat.zero_le c.val |>.trans_lt hcb'
      lia
    have hη' : Relation.EqvGen
        (fun x y => (a ≤ x ∧ x ≤ b') ∧ (a ≤ y ∧ y ≤ b') ∧
          D.edgeData.selected η.val x y) u v := by
      apply Relation.EqvGen.mono ?_ u v hη
      intro x y h
      exact ⟨⟨h.1.1, Nat.le_sub_one_of_lt h.1.2⟩,
        ⟨h.2.1.1, Nat.le_sub_one_of_lt h.2.1.2⟩, h.2.2⟩
    obtain ⟨ξ, hηξ, hξ, hkeep'⟩ := ih _ hlt η b' rfl hcb'' hη'
    exact ⟨ξ, hθη.trans hηξ, hξ,
      fun x y hy hxy => hkeep' x y hy (hkeep x y (hy.trans_lt hcb') hxy)⟩

/-- Raise the lower bound of a weak path while retaining every selected edge above the new bound. -/
theorem exists_weakReach_with_larger_lower_bound (hforward : Forward D)
    (θ : Orientation D) (a b c u v : Fin n)
    (hcu : c ≤ u) (hcv : c ≤ v) (hub : u ≤ b) (hac : a ≤ c)
    (hweak : Relation.EqvGen
      (fun x y => (a ≤ x ∧ x ≤ b) ∧ (a ≤ y ∧ y ≤ b) ∧
        D.edgeData.selected θ.val x y) u v) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      Relation.EqvGen
        (fun x y => (c ≤ x ∧ x ≤ b) ∧ (c ≤ y ∧ y ≤ b) ∧
          D.edgeData.selected η.val x y) u v ∧
      ∀ x y, c ≤ x → D.edgeData.selected θ.val x y → D.edgeData.selected η.val x y := by
  suffices aux : ∀ N, ∀ (θ : Orientation D) (a : Fin n), c.val - a.val = N → a ≤ c →
      Relation.EqvGen
        (fun x y => (a ≤ x ∧ x ≤ b) ∧ (a ≤ y ∧ y ≤ b) ∧
          D.edgeData.selected θ.val x y) u v →
      ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
        Relation.EqvGen
          (fun x y => (c ≤ x ∧ x ≤ b) ∧ (c ≤ y ∧ y ≤ b) ∧
            D.edgeData.selected η.val x y) u v ∧
        ∀ x y, c ≤ x → D.edgeData.selected θ.val x y → D.edgeData.selected η.val x y by
    exact aux _ θ a rfl hac hweak
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro θ a hN hac hweak
    by_cases heq : a = c
    · subst a
      exact ⟨θ, Relation.ReflTransGen.refl, hweak, fun _ _ _ h => h⟩
    have hac' : a < c := lt_of_le_of_ne hac heq
    obtain ⟨η, hθη, hη, hkeep⟩ := exists_weakReach_above hforward θ a b u v
      (hac'.trans_le hcu) (hac'.trans_le hcv) hub hweak
    let a' : Fin n := ⟨a.val + 1, (Nat.succ_le_of_lt hac').trans_lt c.isLt⟩
    have hac'' : a' ≤ c := Nat.succ_le_of_lt hac'
    have hlt : c.val - a'.val < N := by
      change c.val - (a.val + 1) < N
      have hval : a.val < c.val := hac'
      lia
    have hη' : Relation.EqvGen
        (fun x y => (a' ≤ x ∧ x ≤ b) ∧ (a' ≤ y ∧ y ≤ b) ∧
          D.edgeData.selected η.val x y) u v := by
      apply Relation.EqvGen.mono ?_ u v hη
      intro x y h
      exact ⟨⟨Nat.succ_le_of_lt h.1.1, h.1.2⟩,
        ⟨Nat.succ_le_of_lt h.2.1.1, h.2.1.2⟩, h.2.2⟩
    obtain ⟨ξ, hηξ, hξ, hkeep'⟩ := ih _ hlt η a' rfl hac'' hη'
    exact ⟨ξ, hθη.trans hηξ, hξ,
      fun x y hx hxy => hkeep' x y hx (hkeep x y (hac'.trans_le hx) hxy)⟩

/-- Shrinking the upper and then lower bounds puts a weak path inside `[u,v]`. -/
theorem exists_weakReach_within_endpoints (hforward : Forward D)
    (θ : Orientation D) (a b u v : Fin n) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hweak : Relation.EqvGen
      (fun x y => (a ≤ x ∧ x ≤ b) ∧ (a ≤ y ∧ y ≤ b) ∧
        D.edgeData.selected θ.val x y) u v) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      Relation.EqvGen
        (fun x y => (u ≤ x ∧ x ≤ v) ∧ (u ≤ y ∧ y ≤ v) ∧
          D.edgeData.selected η.val x y) u v := by
  obtain ⟨η, hθη, hη, _⟩ := exists_weakReach_with_smaller_upper_bound hforward
    θ a b v u v hau huv le_rfl hvb hweak
  obtain ⟨ξ, hηξ, hξ, _⟩ := exists_weakReach_with_larger_lower_bound hforward
    η a v u u v le_rfl huv huv hau hη
  exact ⟨ξ, hθη.trans hηξ, hξ⟩

end VerticalStripLLT.Circular.DiagramProof
