import VerticalStripLLT.Components.DiagramProof.IntervalReachability
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Simple Hasse paths representing selected weak connections inside a convex set. -/

namespace VerticalStripLLT.Circular.DiagramProof

section Graphs

variable {V : Type*} {G : SimpleGraph V} {R : V → V → Prop}

/-- Map a walk into weak reachability using only its own vertices and edges. -/
theorem eqvGen_of_walk {u v : V} (p : G.Walk u v)
    (hmap : ∀ x y, x ∈ p.support → y ∈ p.support → G.Adj x y → Relation.EqvGen R x y) :
    Relation.EqvGen R u v := by
  induction p with
  | nil => exact Relation.EqvGen.refl _
  | @cons x y z h q ih =>
    exact Relation.EqvGen.trans _ _ _
      (hmap x y (by simp) (by simp) h)
      (ih (fun a b ha hb hab => hmap a b (by simp [ha]) (by simp [hb]) hab))

/-- Symmetrizing a relation as a simple graph does not change weak reachability. -/
theorem eqvGen_iff_fromRel_reachable (u v : V) :
    Relation.EqvGen R u v ↔ (SimpleGraph.fromRel R).Reachable u v := by
  constructor
  · intro h
    induction h with
    | rel x y hxy =>
      by_cases heq : x = y
      · subst y
        exact SimpleGraph.Reachable.refl _
      · exact ⟨SimpleGraph.Walk.cons ⟨heq, Or.inl hxy⟩ SimpleGraph.Walk.nil⟩
    | refl => exact SimpleGraph.Reachable.refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · rintro ⟨p⟩
    apply eqvGen_of_walk p
    intro x y _ _ hxy
    rcases hxy.2 with h | h
    · exact Relation.EqvGen.rel _ _ h
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h)

/-- A weak connection restricts to any set containing its whole weak block. -/
theorem eqvGen_within_of_class_subset (S : Set V) {u v : V} (huv : Relation.EqvGen R u v)
    (hclass : ∀ w, Relation.EqvGen R u w → S w) :
    Relation.EqvGen (fun x y => S x ∧ S y ∧ R x y) u v := by
  induction huv with
  | rel x y hxy =>
    exact Relation.EqvGen.rel _ _ ⟨hclass x (Relation.EqvGen.refl _),
      hclass y (Relation.EqvGen.rel _ _ hxy), hxy⟩
  | refl => exact Relation.EqvGen.refl _
  | symm x y hxy ih =>
    exact Relation.EqvGen.symm _ _ (ih (fun w hxw => hclass w
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hxy) hxw)))
  | trans x y z hxy _ ih₁ ih₂ =>
    exact Relation.EqvGen.trans _ _ _ (ih₁ hclass)
      (ih₂ (fun w hyw => hclass w (Relation.EqvGen.trans _ _ _ hxy hyw)))

end Graphs

variable {n : ℕ} {D : Diagram n}

/-- The undirected Hasse graph induced on a specified vertex set. -/
def coverGraphWithin (S : Set (Fin n)) (θ : Orientation D) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun x y => S x ∧ S y ∧ Cover θ x y)

theorem coverGraphWithin_adj_iff (S : Set (Fin n)) (θ : Orientation D) (x y : Fin n) :
    (coverGraphWithin S θ).Adj x y ↔ S x ∧ S y ∧ (Cover θ x y ∨ Cover θ y x) := by
  constructor
  · rintro ⟨_, h | h⟩
    · exact ⟨h.1, h.2.1, Or.inl h.2.2⟩
    · exact ⟨h.2.1, h.1, Or.inr h.2.2⟩
  · rintro ⟨hx, hy, h | h⟩
    · exact ⟨h.1.ne, Or.inl ⟨hx, hy, h⟩⟩
    · exact ⟨h.1.ne.symm, Or.inr ⟨hy, hx, h⟩⟩

/-- Every vertex of an induced Hasse walk lies in the inducing set. -/
theorem mem_of_coverGraphWithin_support {S : Set (Fin n)} {θ : Orientation D}
    {u v : Fin n} (p : (coverGraphWithin S θ).Walk u v) (hu : S u) :
    ∀ z, z ∈ p.support → S z := by
  induction p with
  | nil =>
    intro z hz
    simpa using (SimpleGraph.Walk.mem_support_nil_iff.mp hz) ▸ hu
  | @cons x y z h q ih =>
    have hy := ((coverGraphWithin_adj_iff S θ x y).mp h).2.1
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hu
    · exact ih hy w hw

/-- Selected weak connections in a convex set admit simple Hasse paths in that same set. -/
theorem exists_coverPath_within (hforward : Forward D) (S : Set (Fin n))
    (hconvex : ∀ x y z, S x → S y → x ≤ z → z ≤ y → S z)
    (θ : Orientation D) (u v : Fin n)
    (hweak : Relation.EqvGen
      (fun x y => S x ∧ S y ∧ D.edgeData.selected θ.val x y) u v) :
    ∃ p : (coverGraphWithin S θ).Walk u v, p.IsPath := by
  have hc := (weakReach_covers_within_iff hforward S hconvex θ u v).mpr hweak
  exact ((eqvGen_iff_fromRel_reachable u v).mp hc).exists_isPath

/-- A Hasse walk remains a selected weak connection when all its edges are retained. -/
theorem weakReach_of_coverWalk (hforward : Forward D) {S T : Set (Fin n)}
    {θ η : Orientation D} {u v : Fin n} (p : (coverGraphWithin S θ).Walk u v)
    (hvertices : ∀ z, z ∈ p.support → T z)
    (hkeep : ∀ x y, T x → T y → D.edgeData.selected θ.val x y →
      D.edgeData.selected η.val x y) :
    Relation.EqvGen (fun x y => T x ∧ T y ∧ D.edgeData.selected η.val x y) u v := by
  apply eqvGen_of_walk p
  intro x y hx hy hxy
  have hxT := hvertices x hx
  have hyT := hvertices y hy
  rcases ((coverGraphWithin_adj_iff S θ x y).mp hxy).2.2 with h | h
  · exact Relation.EqvGen.rel _ _ ⟨hxT, hyT, hkeep x y hxT hyT
      (selected_of_cover hforward h)⟩
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨hyT, hxT,
      hkeep y x hyT hxT (selected_of_cover hforward h)⟩)

end VerticalStripLLT.Circular.DiagramProof
