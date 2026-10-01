import VerticalStripLLT.Components.DiagramProof.Foundation.WeakBlocks

/-! Flips whose three vertices lie in a prescribed set preserve its induced weak blocks. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

variable {n : ℕ} {D : Diagram n}

/-- A directed flip with all three vertices in the specified set. -/
def DirectedFlipWithin (S : Set (Fin n)) (θ η : Orientation D) : Prop :=
  ∃ w : DirectedFlipWitness D θ η, S w.eab.tail ∧ S w.eab.head ∧ S w.ebc.head

theorem DirectedFlipWithin.directedFlip {S : Set (Fin n)} {θ η : Orientation D}
    (h : DirectedFlipWithin S θ η) : DirectedFlip D θ η := ⟨h.choose⟩

/-- A triangle exchange inside a set preserves every weak block of its induced graph. -/
theorem weakReach_within_iff_of_directedFlip {S : Set (Fin n)} {θ η : Orientation D}
    (w : DirectedFlipWitness D θ η)
    (ha : S w.eab.tail) (hb : S w.eab.head) (hc : S w.ebc.head) (u v : Fin n) :
    Relation.EqvGen (fun x y => S x ∧ S y ∧ D.edgeData.selected θ.val x y) u v ↔
      Relation.EqvGen (fun x y => S x ∧ S y ∧ D.edgeData.selected η.val x y) u v := by
  let R := fun x y => S x ∧ S y ∧ D.edgeData.selected θ.val x y
  let T := fun x y => S x ∧ S y ∧ D.edgeData.selected η.val x y
  have longθ : R w.eab.tail w.ebc.head :=
    ⟨ha, hc, w.longEdge, w.longEdge_mem, w.longEdge_tail.symm, w.longEdge_head.symm⟩
  have longη : T w.eab.tail w.ebc.head :=
    ⟨ha, hc, w.longEdge, w.longEdge_target_mem, w.longEdge_tail.symm,
      w.longEdge_head.symm⟩
  have shortθ : R w.eab.tail w.eab.head :=
    ⟨ha, hb, w.eab, Finset.mem_union_right _ w.source_ab_mem, rfl, rfl⟩
  have shortη : T w.eab.head w.ebc.head :=
    ⟨hb, hc, w.ebc, Finset.mem_union_right _ w.target_bc_mem, w.short_head_tail.symm, rfl⟩
  have forward : ∀ x y, R x y → Relation.EqvGen T x y := by
    rintro x y ⟨hx, hy, e, he, rfl, rfl⟩
    by_cases hab : e = w.eab
    · subst e
      exact (Relation.EqvGen.rel _ _ longη).trans _ _ _
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ shortη))
    · apply Relation.EqvGen.rel
      refine ⟨hx, hy, e, ?_, rfl, rfl⟩
      change e ∈ D.strict ∪ η.val
      rw [w.full_target_eq_source_swap]
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hab, he⟩)
  have backward : ∀ x y, T x y → Relation.EqvGen R x y := by
    rintro x y ⟨hx, hy, e, he, rfl, rfl⟩
    by_cases hbc : e = w.ebc
    · subst e
      change Relation.EqvGen R w.ebc.tail w.ebc.head
      rw [← w.short_head_tail]
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ shortθ))
        (Relation.EqvGen.rel _ _ longθ)
    · apply Relation.EqvGen.rel
      refine ⟨hx, hy, e, ?_, rfl, rfl⟩
      change e ∈ D.strict ∪ η.val at he
      rw [w.full_target_eq_source_swap] at he
      exact (Finset.mem_erase.mp ((Finset.mem_insert.mp he).resolve_left hbc)).2
  exact ⟨Relation.EqvGen.eqvGen_le forward u v, Relation.EqvGen.eqvGen_le backward u v⟩

/-- Edges outside the induced set are unchanged by a flip within it. -/
theorem selected_outside_iff_of_directedFlip {S : Set (Fin n)} {θ η : Orientation D}
    (w : DirectedFlipWitness D θ η)
    (ha : S w.eab.tail) (hb : S w.eab.head) (hc : S w.ebc.head)
    (u v : Fin n) (hout : ¬ (S u ∧ S v)) :
    D.edgeData.selected η.val u v ↔ D.edgeData.selected θ.val u v := by
  have hmem (e : Edge D.area) (het : e.tail = u) (heh : e.head = v) :
      e ∈ D.strict ∪ η.val ↔ e ∈ D.strict ∪ θ.val := by
    have hab : e ≠ w.eab := by
      intro he
      subst e
      exact hout ⟨het ▸ ha, heh ▸ hb⟩
    have hbc : e ≠ w.ebc := by
      intro he
      subst e
      exact hout ⟨het ▸ w.short_head_tail ▸ hb, heh ▸ hc⟩
    rw [w.full_target_eq_source_swap]
    simp [hab, hbc]
  constructor
  · rintro ⟨e, he, het, heh⟩
    exact ⟨e, (hmem e het heh).mp he, het, heh⟩
  · rintro ⟨e, he, het, heh⟩
    exact ⟨e, (hmem e het heh).mpr he, het, heh⟩

/-- A reverse path within a set is an actual flip path in the ambient diagram. -/
theorem flip_reachable_of_reverse_directed_within {S : Set (Fin n)} {θ η : Orientation D}
    (hp : Relation.ReflTransGen (fun α β => DirectedFlipWithin S β α) θ η) :
    Relation.ReflTransGen (Flip D) θ η :=
  Relation.ReflTransGen.mono (fun _ _ h => Or.inr h.directedFlip) _ _ hp

/-- Such paths preserve induced weak blocks in every set containing their vertices. -/
theorem weakReach_within_iff_of_reverse_directed_reachable
    {S T : Set (Fin n)} (hST : S ⊆ T) {θ η : Orientation D}
    (hp : Relation.ReflTransGen (fun α β => DirectedFlipWithin S β α) θ η) (u v : Fin n) :
    Relation.EqvGen (fun x y => T x ∧ T y ∧ D.edgeData.selected θ.val x y) u v ↔
      Relation.EqvGen (fun x y => T x ∧ T y ∧ D.edgeData.selected η.val x y) u v := by
  induction hp with
  | refl => exact Iff.rfl
  | tail _ hstep ih =>
    obtain ⟨w, ha, hb, hc⟩ := hstep
    exact ih.trans (weakReach_within_iff_of_directedFlip w
      (hST ha) (hST hb) (hST hc) u v).symm

/-- Reverse paths within a set leave every exterior selected edge fixed. -/
theorem selected_outside_iff_of_reverse_directed_reachable
    {S : Set (Fin n)} {θ η : Orientation D}
    (hp : Relation.ReflTransGen (fun α β => DirectedFlipWithin S β α) θ η)
    (u v : Fin n) (hout : ¬ (S u ∧ S v)) :
    D.edgeData.selected η.val u v ↔ D.edgeData.selected θ.val u v := by
  induction hp with
  | refl => exact Iff.rfl
  | tail _ hstep ih =>
    obtain ⟨w, ha, hb, hc⟩ := hstep
    exact (selected_outside_iff_of_directedFlip w ha hb hc u v hout).symm.trans ih

end VerticalStripLLT.Circular.DiagramProof
