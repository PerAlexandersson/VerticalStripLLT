import VerticalStripLLT.Components.DiagramProof.CliqueBlockReplacement
import VerticalStripLLT.Components.DiagramProof.SubsetEmbedding

/-! Enumerating a selected weak block inside a natural clique interval. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n}

theorem exists_clique_block_embedding (e : Edge D.area) (θ : Orientation D)
    (z : Fin n) (hz : e.tail ≤ z ∧ z ≤ e.head) :
    ∃ k, ∃ ι : Fin (k + 1) ↪o Fin n,
      (∀ i, e.tail ≤ ι i ∧ ι i ≤ e.head) ∧
      (∃ i, ι i = z) ∧
      ∀ w, (∃ i, ι i = w) ↔
        Relation.EqvGen (cliqueBlockRelation e θ) (ι 0) w := by
  let R := cliqueBlockRelation e θ
  have hbound : ∀ x y, Relation.EqvGen R x y →
      ((e.tail ≤ x ∧ x ≤ e.head) ↔ (e.tail ≤ y ∧ y ≤ e.head)) := by
    intro x y hxy
    induction hxy with
    | refl => exact Iff.rfl
    | rel x y hxy => exact ⟨fun _ => hxy.2.1, fun _ => hxy.1⟩
    | symm x y hxy ih => exact ih.symm
    | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  let s : Finset (Fin n) := Finset.univ.filter (fun w => Relation.EqvGen R z w)
  have hs : s.Nonempty := by
    exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.EqvGen.refl _⟩⟩
  obtain ⟨k, ι, himage⟩ := exists_orderEmbedding_of_nonempty_finset s hs
  refine ⟨k, ι, ?_, ?_, ?_⟩
  · intro i
    have hi := (himage (ι i)).mp ⟨i, rfl⟩
    exact (hbound z (ι i) (Finset.mem_filter.mp hi).2).mp hz
  · obtain ⟨i, hi⟩ := (himage z).mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Relation.EqvGen.refl _⟩)
    exact ⟨i, hi⟩
  · intro w
    have h0 : Relation.EqvGen R z (ι 0) :=
      (Finset.mem_filter.mp ((himage (ι 0)).mp ⟨0, rfl⟩)).2
    constructor
    · intro hw
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h0)
        (Finset.mem_filter.mp ((himage w).mp hw)).2
    · intro hw
      have hwz : Relation.EqvGen R z w := by
        exact Relation.EqvGen.trans _ _ _ h0 hw
      exact (himage w).mpr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hwz⟩)

end

end VerticalStripLLT.Circular.DiagramProof
