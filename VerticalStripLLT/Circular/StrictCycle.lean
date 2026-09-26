import VerticalStripLLT.Circular.EdgeColoring
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card

/-! Vanishing from a strict edge entering every vertex. -/

namespace VerticalStripLLT.Circular.EdgeData

variable {V E : Type*}

/-- Incoming strict edges at every vertex prevent every selected relation from being acyclic. -/
theorem not_Admissible_of_strict_incoming [Finite V] [Nonempty V] [DecidableEq E]
    (G : EdgeData V E) (hin : ∀ v, ∃ e ∈ G.strict, G.head e = v) (A : Finset E) :
    ¬ G.Admissible A := by
  classical
  intro hA
  let : IsTrans V (Relation.TransGen (G.selected A)) :=
    ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
  let : Std.Irrefl (Relation.TransGen (G.selected A)) := ⟨hA⟩
  have hwf := Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen (G.selected A))
  apply hwf.induction (C := fun _ => False) (Classical.arbitrary V)
  intro v ih
  obtain ⟨e, he, hv⟩ := hin v
  exact ih (G.tail e) (Relation.TransGen.single
    ⟨e, Finset.mem_union_left _ he, rfl, hv⟩)

/-- A strict edge entering every vertex makes a strict coloring impossible. -/
theorem not_admissibleColoring_of_strict_incoming [Fintype V] [Nonempty V]
    (G : EdgeData V E) (hin : ∀ v, ∃ e ∈ G.strict, G.head e = v) {m : ℕ}
    (c : V → Fin m) : ¬ G.admissibleColoring c := by
  classical
  obtain ⟨v, _, hvmin⟩ := Finset.exists_min_image Finset.univ c Finset.univ_nonempty
  obtain ⟨e, he, hhead⟩ := hin v
  intro hc
  have hmin : c v ≤ c (G.tail e) := hvmin (G.tail e) (Finset.mem_univ _)
  have hstrict := hc e he
  rw [hhead] at hstrict
  exact (not_lt_of_ge hmin) hstrict

/-- Every finite-alphabet coloring LLT vanishes when each vertex has an incoming strict edge. -/
theorem coloringLLT_eq_zero_of_strict_incoming [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdgeData V E)
    (hin : ∀ v, ∃ e ∈ G.strict, G.head e = v) (m : ℕ) :
    G.coloringLLT m = 0 := by
  classical
  unfold coloringLLT
  apply Finset.sum_eq_zero
  intro c _
  simp [coloringWeight, G.not_admissibleColoring_of_strict_incoming hin c]

end VerticalStripLLT.Circular.EdgeData
