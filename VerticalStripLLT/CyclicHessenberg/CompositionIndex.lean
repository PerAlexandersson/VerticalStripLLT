import Mathlib.Combinatorics.Enumerative.Composition

set_option autoImplicit false

/-! Order facts for the block index and embeddings of a composition. -/

namespace Composition

variable {n : ℕ} (c : Composition n)

/-- The block index is monotone along the ambient ordered positions. -/
theorem index_monotone : Monotone c.index := by
  intro x y hxy
  apply Fin.le_iff_val_le_val.mpr
  by_contra hnot
  have hidx : (c.index y : ℕ) < c.index x := Nat.lt_of_not_ge hnot
  have hstep : (c.index y : ℕ) + 1 ≤ c.index x := Nat.succ_le_of_lt hidx
  have hsize := c.monotone_sizeUpTo hstep
  have hy : (y : ℕ) < c.sizeUpTo (c.index y).succ := c.lt_sizeUpTo_index_succ y
  have hx : c.sizeUpTo (c.index x) ≤ (x : ℕ) := c.sizeUpTo_index_le x
  have hxy' : (x : ℕ) ≤ y := Fin.le_iff_val_le_val.mp hxy
  have hyx : (y : ℕ) < (x : ℕ) := lt_of_lt_of_le hy (le_trans hsize hx)
  exact (not_lt_of_ge hxy') hyx

/-- Every block is nonempty, so the index map is surjective by embedding position zero. -/
theorem index_surjective : Function.Surjective c.index := by
  intro i
  have hpos : 0 < c.blocksFun i :=
    lt_of_lt_of_le Nat.zero_lt_one (c.one_le_blocksFun i)
  let j : Fin (c.blocksFun i) := ⟨0, hpos⟩
  exact ⟨c.embedding i j, c.index_embedding i j⟩

/-- Two ambient positions have the same block index exactly when they lie in a common block. -/
theorem index_eq_iff_same_block {x y : Fin n} :
    c.index x = c.index y ↔
      ∃ i : Fin c.length,
        x ∈ Set.range (c.embedding i) ∧ y ∈ Set.range (c.embedding i) := by
  constructor
  · intro h
    refine ⟨c.index x, c.mem_range_embedding x, ?_⟩
    rw [c.mem_range_embedding_iff']
    exact h
  · rintro ⟨i, hx, hy⟩
    have hxi := c.mem_range_embedding_iff'.mp hx
    have hyi := c.mem_range_embedding_iff'.mp hy
    exact hxi.symm.trans hyi

/-- The increasing block embedding preserves and reflects strict order. -/
theorem embedding_lt_iff (i : Fin c.length) (a b : Fin (c.blocksFun i)) :
    c.embedding i a < c.embedding i b ↔ a < b :=
  (c.embedding i).lt_iff_lt

/-- Positions in strictly earlier blocks precede every position in a later block. -/
theorem embedding_lt_of_lt_index {i j : Fin c.length} (hij : i < j)
    (a : Fin (c.blocksFun i)) (b : Fin (c.blocksFun j)) :
    c.embedding i a < c.embedding j b := by
  apply Fin.lt_iff_val_lt_val.mpr
  rw [c.coe_embedding, c.coe_embedding]
  have hi : c.sizeUpTo i + a < c.sizeUpTo (i : ℕ) + c.blocksFun i :=
    Nat.add_lt_add_left a.isLt _
  rw [← c.sizeUpTo_succ' i] at hi
  have hstep : (i : ℕ) + 1 ≤ j :=
    Nat.succ_le_of_lt (Fin.lt_iff_val_lt_val.mp hij)
  have hsize := c.monotone_sizeUpTo hstep
  exact lt_of_lt_of_le hi (le_trans hsize (Nat.le_add_right _ _))

end Composition
