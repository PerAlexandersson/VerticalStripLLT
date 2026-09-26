import VerticalStripLLT.Circular.InteriorComponentIsolation
import VerticalStripLLT.Circular.InteriorColumnGeometry
import VerticalStripLLT.Circular.ColumnIndexReversal
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-! Reverse each circular column of the merged interior strict component. -/

namespace VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

open scoped Classical

variable {n r j : ℕ} {D : Diagram n} {t : ℤ}
  (K : InteriorMergedComponent D t r j)

/-- Reverse each index column and fix all vertices outside the merged component. -/
noncomputable def reversalPerm : Equiv.Perm (Fin n) :=
  Equiv.Perm.viaEmbedding (columnReversePerm (r + j) j (by have := K.two_le; lia))
    K.vertexEmbedding

theorem reversalPerm_vertex (a : Fin (r + j)) :
    K.reversalPerm (K.vertex a.val) =
      K.vertex (columnReverseIndex (r + j) j (a.val % j) (a.val / j)) := by
  exact Equiv.Perm.viaEmbedding_apply
    (columnReversePerm (r + j) j (by have := K.two_le; lia)) K.vertexEmbedding a

theorem reversalPerm_fixed (v : Fin n) (hv : v ∉ K.componentVertices) :
    K.reversalPerm v = v := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨a, ha⟩
  exact hv ((K.mem_componentVertices_iff v).mpr ⟨a, ha⟩)

theorem reversalPerm_involutive : Function.Involutive K.reversalPerm := by
  intro v
  by_cases hv : v ∈ K.componentVertices
  · obtain ⟨a, rfl⟩ := (K.mem_componentVertices_iff v).mp hv
    have hj : 0 < j := by have := K.two_le; lia
    have h1 := Equiv.Perm.viaEmbedding_apply (columnReversePerm (r + j) j hj)
      K.vertexEmbedding a
    have h2 := Equiv.Perm.viaEmbedding_apply (columnReversePerm (r + j) j hj)
      K.vertexEmbedding (columnReversePerm (r + j) j hj a)
    change K.reversalPerm (K.vertex a.val) =
      K.vertexEmbedding (columnReversePerm (r + j) j hj a) at h1
    rw [h1]
    exact h2.trans (congrArg K.vertexEmbedding
      (columnReverseFin_involutive (r + j) j hj a))
  · rw [K.reversalPerm_fixed v hv, K.reversalPerm_fixed v hv]

/-- Reversal stays in the same circular column, with reflected row index. -/
theorem reversalPerm_column (c h : ℕ) (hc : c < j) (hh : c + j * h < r + j) :
    K.reversalPerm (K.vertex (c + j * h)) =
      K.vertex (c + j * (colLen (r + j) j c - 1 - h)) := by
  have hj : 0 < j := by have := K.two_le; lia
  have hval := columnReversePerm_at hj hc hh
  have he := Equiv.Perm.viaEmbedding_apply (columnReversePerm (r + j) j hj)
    K.vertexEmbedding ⟨c + j * h, hh⟩
  change K.reversalPerm (K.vertex (c + j * h)) =
    K.vertex (columnReversePerm (r + j) j hj ⟨c + j * h, hh⟩).val at he
  rw [hval] at he
  exact he

end VerticalStripLLT.Circular.Diagram.InteriorMergedComponent
