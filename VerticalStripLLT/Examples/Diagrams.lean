import VerticalStripLLT.Circular.Diagram

/-! Concrete circular diagrams for examples, outside the general theorem layer. -/

namespace VerticalStripLLT.Circular.Diagram

noncomputable section

def constantAreaOne : CircularArea 2 where
  positive := by decide
  area := fun _ => 1
  bound := by intro i; decide
  cyclic := by intro i; simp

/-- The constant-area-one circular diagram with an arbitrary strict subset. -/
def twoEdge (i : Fin 2) : Edge constantAreaOne :=
  ⟨(i, ⟨1, by decide⟩), by simp [constantAreaOne]⟩

@[simp] theorem twoEdge_head (i : Fin 2) : (twoEdge i).head = i := rfl

@[simp] theorem twoEdge_length (i : Fin 2) : (twoEdge i).length.val = 1 := rfl

@[simp] theorem twoEdge_tail (i : Fin 2) : (twoEdge i).tail.val = (i.val + 1) % 2 := by
  rfl

theorem edge_eq_twoEdge_head (e : Edge constantAreaOne) : e = twoEdge e.head := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Fin.ext
    exact Nat.le_antisymm e.2.2 e.2.1

/-- The constant-area-one circular diagram with an arbitrary strict subset. -/
def twoCycle (S : Finset (Fin 2)) : Diagram 2 where
  area := constantAreaOne
  strict := S.image twoEdge
  strict_corner := by
    intro e he
    have hlen : e.length.val = 1 := by
      exact Nat.le_antisymm e.2.2 e.2.1
    constructor
    · simpa [constantAreaOne] using hlen
    · simp [constantAreaOne, CircularArea.next]

/-- No strict edges in the size-two constant-area-one cycle. -/
def noStrict : Diagram 2 := twoCycle ∅

/-- The edge with tail `0`, head `1`, and length one is strict. -/
def oneStrict : Diagram 2 := twoCycle {1}

/-- Both admissible edges are strict. -/
def bothStrict : Diagram 2 := twoCycle Finset.univ

@[simp] theorem noStrict_strict : noStrict.strict = ∅ := by
  exact Finset.image_empty twoEdge

@[simp] theorem oneStrict_mem :
    twoEdge 1
      ∈ oneStrict.strict := by
  exact Finset.mem_image.mpr ⟨1, Finset.mem_singleton_self _, rfl⟩

end

end VerticalStripLLT.Circular.Diagram
