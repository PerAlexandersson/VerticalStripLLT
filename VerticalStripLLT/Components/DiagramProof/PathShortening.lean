import VerticalStripLLT.Components.DiagramProof.HassePaths
import VerticalStripLLT.Components.DiagramProof.PathSplit

/-! Remove an internal extreme vertex from a Hasse path by one actual cover flip. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

private theorem exists_incoming_shortcut (hforward : Forward D) (θ : Orientation D)
    (i j b : Fin n) (hib : Cover θ i b) (hjb : Cover θ j b) (hne : i ≠ j) :
    ∃ η : Orientation D, Flip D θ η ∧
      (D.edgeData.selected η.val i j ∨ D.edgeData.selected η.val j i) ∧
      ∀ x y, y ≠ b → D.edgeData.selected θ.val x y → D.edgeData.selected η.val x y := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · obtain ⟨η, hf, _, hc, hs⟩ :=
      exists_incomingSwap_of_covers hforward θ i j b hjb hib hij
    refine ⟨η, hf, Or.inl (selected_of_cover hforward hc), ?_⟩
    intro x y hy hxy
    exact (hs x y).mpr (Or.inr ⟨hxy, fun h => hy h.2⟩)
  · obtain ⟨η, hf, _, hc, hs⟩ :=
      exists_incomingSwap_of_covers hforward θ j i b hib hjb hji
    refine ⟨η, hf, Or.inr (selected_of_cover hforward hc), ?_⟩
    intro x y hy hxy
    exact (hs x y).mpr (Or.inr ⟨hxy, fun h => hy h.2⟩)

private theorem exists_outgoing_shortcut (hforward : Forward D) (θ : Orientation D)
    (a i j : Fin n) (hai : Cover θ a i) (haj : Cover θ a j) (hne : i ≠ j) :
    ∃ η : Orientation D, Flip D θ η ∧
      (D.edgeData.selected η.val i j ∨ D.edgeData.selected η.val j i) ∧
      ∀ x y, x ≠ a → D.edgeData.selected θ.val x y → D.edgeData.selected η.val x y := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · obtain ⟨η, hf, _, hc, hs⟩ :=
      exists_outgoingSwap_of_covers hforward θ a i j hai haj hij
    refine ⟨η, hf, Or.inl (selected_of_cover hforward hc), ?_⟩
    intro x y hx hxy
    exact (hs x y).mpr (Or.inr ⟨hxy, fun h => hx h.1⟩)
  · obtain ⟨η, hf, _, hc, hs⟩ :=
      exists_outgoingSwap_of_covers hforward θ a j i haj hai hji
    refine ⟨η, hf, Or.inr (selected_of_cover hforward hc), ?_⟩
    intro x y hx hxy
    exact (hs x y).mpr (Or.inr ⟨hxy, fun h => hx h.1⟩)

/-- A weak connection in `[a,b]` with both ends below `b` can be moved into `[a,b)`.
No previously selected edge whose head is below `b` is removed. -/
theorem exists_weakReach_below (hforward : Forward D) (θ : Orientation D)
    (a b u v : Fin n) (hau : a ≤ u) (hub : u < b) (hvb : v < b)
    (hweak : Relation.EqvGen
      (fun x y => (a ≤ x ∧ x ≤ b) ∧ (a ≤ y ∧ y ≤ b) ∧
        D.edgeData.selected θ.val x y) u v) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      Relation.EqvGen
        (fun x y => (a ≤ x ∧ x < b) ∧ (a ≤ y ∧ y < b) ∧
          D.edgeData.selected η.val x y) u v ∧
      ∀ x y, y < b → D.edgeData.selected θ.val x y → D.edgeData.selected η.val x y := by
  classical
  let S : Set (Fin n) := {x | a ≤ x ∧ x ≤ b}
  let T : Set (Fin n) := {x | a ≤ x ∧ x < b}
  obtain ⟨p, hp⟩ := exists_coverPath_within hforward S
    (fun _ _ _ hx hy hxz hzy => ⟨hx.1.trans hxz, hzy.trans hy.2⟩) θ u v hweak
  have hbounds := mem_of_coverGraphWithin_support p (show S u from ⟨hau, hub.le⟩)
  have hT (x : Fin n) (hx : x ∈ p.support) (hne : x ≠ b) : T x :=
    ⟨(hbounds x hx).1, lt_of_le_of_ne (hbounds x hx).2 hne⟩
  by_cases hb : b ∈ p.support
  · obtain ⟨i, j, r, s, hib, hbj, hne, hr, hs⟩ :=
      exists_path_split_at_internal_vertex p hp hb hub.ne.symm hvb.ne.symm
    have hi := (coverGraphWithin_adj_iff S θ i b).mp hib
    have hj := (coverGraphWithin_adj_iff S θ b j).mp hbj
    have hic : Cover θ i b := hi.2.2.resolve_right
      (fun h => not_lt_of_ge hi.1.2 h.1)
    have hjc : Cover θ j b := hj.2.2.resolve_left
      (fun h => not_lt_of_ge hj.2.1.2 h.1)
    obtain ⟨η, hf, hij, hkeep⟩ := exists_incoming_shortcut hforward θ i j b hic hjc hne
    have hrT : ∀ x, x ∈ r.support → T x := fun x hx => hT x (hr x hx).1 (hr x hx).2
    have hsT : ∀ x, x ∈ s.support → T x := fun x hx => hT x (hs x hx).1 (hs x hx).2
    have keep : ∀ x y, T x → T y → D.edgeData.selected θ.val x y →
        D.edgeData.selected η.val x y := fun x y _ hy => hkeep x y hy.2.ne
    have left := weakReach_of_coverWalk hforward r hrT keep
    have right := weakReach_of_coverWalk hforward s hsT keep
    have middle : Relation.EqvGen
        (fun x y => T x ∧ T y ∧ D.edgeData.selected η.val x y) i j := by
      have hiT := hrT i r.end_mem_support
      have hjT := hsT j s.start_mem_support
      rcases hij with hij | hji
      · exact Relation.EqvGen.rel _ _ ⟨hiT, hjT, hij⟩
      · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨hjT, hiT, hji⟩)
    exact ⟨η, Relation.ReflTransGen.single hf,
      Relation.EqvGen.trans _ _ _ left (Relation.EqvGen.trans _ _ _ middle right),
      fun x y hy => hkeep x y hy.ne⟩
  · refine ⟨θ, Relation.ReflTransGen.refl, ?_, fun _ _ _ h => h⟩
    apply weakReach_of_coverWalk hforward p
      (fun x hx => hT x hx (fun heq => hb (heq ▸ hx)))
    exact fun _ _ _ _ h => h

/-- A weak connection in `[a,b]` with both ends above `a` can be moved into `(a,b]`.
No previously selected edge whose tail is above `a` is removed. -/
theorem exists_weakReach_above (hforward : Forward D) (θ : Orientation D)
    (a b u v : Fin n) (hau : a < u) (hav : a < v) (hub : u ≤ b)
    (hweak : Relation.EqvGen
      (fun x y => (a ≤ x ∧ x ≤ b) ∧ (a ≤ y ∧ y ≤ b) ∧
        D.edgeData.selected θ.val x y) u v) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      Relation.EqvGen
        (fun x y => (a < x ∧ x ≤ b) ∧ (a < y ∧ y ≤ b) ∧
          D.edgeData.selected η.val x y) u v ∧
      ∀ x y, a < x → D.edgeData.selected θ.val x y → D.edgeData.selected η.val x y := by
  classical
  let S : Set (Fin n) := {x | a ≤ x ∧ x ≤ b}
  let T : Set (Fin n) := {x | a < x ∧ x ≤ b}
  obtain ⟨p, hp⟩ := exists_coverPath_within hforward S
    (fun _ _ _ hx hy hxz hzy => ⟨hx.1.trans hxz, hzy.trans hy.2⟩) θ u v hweak
  have hbounds := mem_of_coverGraphWithin_support p (show S u from ⟨hau.le, hub⟩)
  have hT (x : Fin n) (hx : x ∈ p.support) (hne : x ≠ a) : T x :=
    ⟨lt_of_le_of_ne (hbounds x hx).1 hne.symm, (hbounds x hx).2⟩
  by_cases ha : a ∈ p.support
  · obtain ⟨i, j, r, s, hia, haj, hne, hr, hs⟩ :=
      exists_path_split_at_internal_vertex p hp ha hau.ne hav.ne
    have hi := (coverGraphWithin_adj_iff S θ i a).mp hia
    have hj := (coverGraphWithin_adj_iff S θ a j).mp haj
    have hic : Cover θ a i := hi.2.2.resolve_left
      (fun h => not_lt_of_ge hi.1.1 h.1)
    have hjc : Cover θ a j := hj.2.2.resolve_right
      (fun h => not_lt_of_ge hj.2.1.1 h.1)
    obtain ⟨η, hf, hij, hkeep⟩ := exists_outgoing_shortcut hforward θ a i j hic hjc hne
    have hrT : ∀ x, x ∈ r.support → T x := fun x hx => hT x (hr x hx).1 (hr x hx).2
    have hsT : ∀ x, x ∈ s.support → T x := fun x hx => hT x (hs x hx).1 (hs x hx).2
    have keep : ∀ x y, T x → T y → D.edgeData.selected θ.val x y →
        D.edgeData.selected η.val x y := fun x y hx _ => hkeep x y hx.1.ne.symm
    have left := weakReach_of_coverWalk hforward r hrT keep
    have right := weakReach_of_coverWalk hforward s hsT keep
    have middle : Relation.EqvGen
        (fun x y => T x ∧ T y ∧ D.edgeData.selected η.val x y) i j := by
      have hiT := hrT i r.end_mem_support
      have hjT := hsT j s.start_mem_support
      rcases hij with hij | hji
      · exact Relation.EqvGen.rel _ _ ⟨hiT, hjT, hij⟩
      · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨hjT, hiT, hji⟩)
    exact ⟨η, Relation.ReflTransGen.single hf,
      Relation.EqvGen.trans _ _ _ left (Relation.EqvGen.trans _ _ _ middle right),
      fun x y hx => hkeep x y hx.ne.symm⟩
  · refine ⟨θ, Relation.ReflTransGen.refl, ?_, fun _ _ _ h => h⟩
    apply weakReach_of_coverWalk hforward p
      (fun x hx => hT x hx (fun heq => ha (heq ▸ hx)))
    exact fun _ _ _ _ h => h

end VerticalStripLLT.Circular.DiagramProof
