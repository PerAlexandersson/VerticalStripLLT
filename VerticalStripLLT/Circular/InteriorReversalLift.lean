import VerticalStripLLT.Circular.InteriorReversalDisplacement
import VerticalStripLLT.Circular.ColumnDisplacement

/-! The periodic integer lift of column reversal. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram.InteriorMergedComponent

open scoped Classical

variable {n r j : ℕ} {D : Diagram n} {t : ℤ}
  (K : InteriorMergedComponent D t r j)

private theorem residue_add_congr {x y : ℤ} (h : D.residue x = D.residue y) (z : ℤ) :
    D.residue (x + z) = D.residue (y + z) := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  have hh := congrArg (fun v : Fin n => (v.val : ℤ)) h
  simp only [D.residue_coe_val] at hh ⊢
  rw [Int.add_emod x z (n : ℤ), hh, ← Int.add_emod y z (n : ℤ)]

private theorem residue_add_nat (z : ℤ) (h : ℕ) :
    D.residue (z + h) = D.area.atOffset (D.residue z) h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, D.residue_succ, ih,
      D.area.atOffset_succ]

/-- Moving between two rows in one column has its literal integer displacement. -/
theorem residue_column_shift (c h h' : ℕ) (hc : c < j)
    (hh : c + j * h < r + j) (hh' : c + j * h' < r + j)
    (z : ℤ) (hz : D.residue z = K.vertex (c + j * h)) :
    D.residue (z + (h' : ℤ) - h) = K.vertex (c + j * h') := by
  have hbase : D.residue ((K.vertex c).val : ℤ) = K.vertex c := by
    apply Fin.ext
    apply Int.ofNat_inj.mp
    rw [D.residue_coe_val]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast (K.vertex c).isLt)
  have hr : D.residue (((K.vertex c).val : ℤ) + h) = K.vertex (c + j * h) := by
    rw [residue_add_nat, hbase, ← K.vertex_atOffset c h hc hh]
  have hs := residue_add_congr (hz.trans hr.symm) ((h' : ℤ) - h)
  have heq : ((K.vertex c).val : ℤ) + h + ((h' : ℤ) - h) =
      ((K.vertex c).val : ℤ) + h' := by ring
  rw [heq, residue_add_nat, hbase, ← K.vertex_atOffset c h' hc hh'] at hs
  simpa only [sub_eq_add_neg, add_assoc] using hs

/-- Signed displacement on the component, extended by zero on all other vertices. -/
noncomputable def reversalShift (v : Fin n) : ℤ :=
  if h : ∃ a : Fin (r + j), K.vertexEmbedding a = v then
    columnDisplacement (r + j) j (Classical.choose h).val
  else 0

theorem reversalShift_vertex (a : Fin (r + j)) :
    K.reversalShift (K.vertex a.val) = columnDisplacement (r + j) j a.val := by
  have h : ∃ b : Fin (r + j), K.vertexEmbedding b = K.vertex a.val := ⟨a, rfl⟩
  rw [reversalShift, dite_eq_left h]
  have heq : Classical.choose h = a :=
    K.vertexEmbedding.injective (Classical.choose_spec h)
  rw [heq]

theorem reversalShift_of_not_mem (v : Fin n) (hv : v ∉ K.componentVertices) :
    K.reversalShift v = 0 := by
  apply dite_eq_right
  rintro ⟨a, ha⟩
  exact hv ((K.mem_componentVertices_iff v).mpr ⟨a, ha⟩)

/-- The signed shift realizes the actual finite permutation on residues. -/
theorem residue_add_reversalShift (z : ℤ) :
    D.residue (z + K.reversalShift (D.residue z)) = K.reversalPerm (D.residue z) := by
  by_cases hz : D.residue z ∈ K.componentVertices
  · obtain ⟨a, ha⟩ := (K.mem_componentVertices_iff _).mp hz
    have hj : 0 < j := by have := K.two_le; lia
    have hc := Nat.mod_lt a.val hj
    have hrow : a.val / j < colLen (r + j) j (a.val % j) :=
      (lt_colLen_iff hj ((Nat.mod_le _ _).trans_lt a.isLt)).mpr
        (by rw [Nat.mod_add_div]; exact a.isLt)
    have hb := columnReverseIndex_lt hj
      (show a.val % j + j * (a.val / j) < r + j by rw [Nat.mod_add_div]; exact a.isLt)
    have hs := K.residue_column_shift (a.val % j) (a.val / j)
      (colLen (r + j) j (a.val % j) - 1 - a.val / j) hc
      (by rw [Nat.mod_add_div]; exact a.isLt) hb z
      (by rw [Nat.mod_add_div]; exact ha.symm)
    rw [← ha, K.reversalShift_vertex a, K.reversalPerm_vertex a]
    have hd : columnDisplacement (r + j) j a.val =
        ((colLen (r + j) j (a.val % j) - 1 - a.val / j : ℕ) : ℤ) - ((a.val / j : ℕ) : ℤ) := by
      unfold columnDisplacement
      rw [Int.ofNat_sub (by lia), Int.ofNat_sub (by lia)]
      ring
    rw [hd]
    simpa only [columnReverseIndex, sub_eq_add_neg, add_assoc] using hs
  · rw [K.reversalShift_of_not_mem _ hz, add_zero, K.reversalPerm_fixed _ hz]

/-- Displacement is negated when the same column is reversed again. -/
theorem reversalShift_reversalPerm (v : Fin n) :
    K.reversalShift (K.reversalPerm v) = -K.reversalShift v := by
  by_cases hv : v ∈ K.componentVertices
  · obtain ⟨a, rfl⟩ := (K.mem_componentVertices_iff v).mp hv
    have hj : 0 < j := by have := K.two_le; lia
    let b := columnReverseFin (r + j) j hj a
    rw [K.reversalPerm_vertex a]
    change K.reversalShift (K.vertex b.val) = -K.reversalShift (K.vertex a.val)
    rw [K.reversalShift_vertex b, K.reversalShift_vertex a]
    have hc := Nat.mod_lt a.val hj
    have hrow : a.val / j < colLen (r + j) j (a.val % j) :=
      (lt_colLen_iff hj ((Nat.mod_le _ _).trans_lt a.isLt)).mpr
        (by rw [Nat.mod_add_div]; exact a.isLt)
    change columnDisplacement (r + j) j
      (columnReverseIndex (r + j) j (a.val % j) (a.val / j)) = _
    unfold columnDisplacement
    rw [columnReverseIndex_mod_eq _ _ _ _ hc, columnReverseIndex_div hj hc,
      Int.ofNat_sub (by lia), Int.ofNat_sub (by lia)]
    ring
  · rw [K.reversalPerm_fixed v hv, K.reversalShift_of_not_mem v hv, neg_zero]

/-- Reflect every lifted column, with the same displacement in each period. -/
noncomputable def reversalLiftFun (z : ℤ) : ℤ := z + K.reversalShift (D.residue z)

theorem reversalLiftFun_involutive : Function.Involutive K.reversalLiftFun := by
  intro z
  simp only [reversalLiftFun, K.residue_add_reversalShift, K.reversalShift_reversalPerm]
  ring

noncomputable def reversalLift : Equiv.Perm ℤ :=
  Function.Involutive.toPerm K.reversalLiftFun K.reversalLiftFun_involutive

theorem reversalLift_residue (z : ℤ) :
    K.reversalTarget.residue (K.reversalLift z) = K.reversalPerm (D.residue z) := by
  exact K.residue_add_reversalShift z

theorem reversalLift_add_period (z k : ℤ) :
    K.reversalLift (z + (n : ℤ) * k) = K.reversalLift z + (n : ℤ) * k := by
  change z + (n : ℤ) * k + K.reversalShift (D.residue (z + (n : ℤ) * k)) = _
  rw [D.residue_add_period]
  change z + (n : ℤ) * k + K.reversalShift (D.residue z) =
    z + K.reversalShift (D.residue z) + (n : ℤ) * k
  ring

end VerticalStripLLT.Circular.Diagram.InteriorMergedComponent
