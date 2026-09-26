import VerticalStripLLT.Circular.BoundaryRow
import VerticalStripLLT.Circular.LiftCover
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith

/-! Boundary intervals as integer lifts of circular edges. -/

namespace VerticalStripLLT.Circular

open scoped Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- The integer interval occupied by an edge ending at `v`.

This is deliberately named differently from `Diagram.naturalLift`, which is
the existing predicate for a lift of a specified edge instance. -/
def boundaryNaturalLift (u v : ℤ) : Prop :=
  D.boundary v ≤ u ∧ u < v

theorem boundaryNaturalLift_length_pos {u v : ℤ}
    (h : D.boundaryNaturalLift u v) : 0 < v - u := by
  exact sub_pos.mpr h.2

theorem boundaryNaturalLift_length_lt {u v : ℤ}
    (h : D.boundaryNaturalLift u v) : v - u < n := by
  have hperiod := D.self_sub_period_lt_boundary v
  have := h.1
  lia

theorem boundaryNaturalLift_length_le_area {u v : ℤ}
    (h : D.boundaryNaturalLift u v) :
    v - u ≤ (D.area.area (D.residue v) : ℤ) := by
  have hh := h.1
  rw [Diagram.boundary] at hh
  lia

/-- The edge determined by a boundary interval. -/
noncomputable def edgeFromLift (u v : ℤ) (h : D.boundaryNaturalLift u v) :
    Edge D.area := by
  have hpos := D.boundaryNaturalLift_length_pos h
  have hlt := D.boundaryNaturalLift_length_lt h
  have hle := D.boundaryNaturalLift_length_le_area h
  have hcast : ((v - u).toNat : ℤ) = v - u := Int.toNat_of_nonneg hpos.le
  refine ⟨(D.residue v, ⟨(v - u).toNat, ?_⟩), ⟨?_, ?_⟩⟩
  · lia
  · change 0 < (v - u).toNat
    lia
  · change (v - u).toNat ≤ D.area.area (D.residue v)
    lia

@[simp] theorem edgeFromLift_head {u v : ℤ} (h : D.boundaryNaturalLift u v) :
    (D.edgeFromLift u v h).head = D.residue v := rfl

theorem edgeFromLift_length {u v : ℤ} (h : D.boundaryNaturalLift u v) :
    ((D.edgeFromLift u v h).length.val : ℤ) = v - u := by
  have hpos := D.boundaryNaturalLift_length_pos h
  change ((v - u).toNat : ℤ) = v - u
  exact Int.toNat_of_nonneg hpos.le

/-- The endpoints of an edge are determined by a chosen integer lift of its
head and length. -/
theorem residue_tail_of_length {e : Edge D.area} {u v : ℤ}
    (hh : e.head = D.residue v)
    (hlen : (e.length.val : ℤ) = v - u) : e.tail = D.residue u := by
  have hsum : u + (e.length.val : ℤ) = v := by
    rw [hlen]
    ring
  have hleft : u + (e.length.val : ℤ) ≡
      (e.head.val : ℤ) [ZMOD (n : ℤ)] := by
    change (u + (e.length.val : ℤ)) % (n : ℤ) =
      (e.head.val : ℤ) % (n : ℤ)
    rw [hsum]
    have hv := D.residue_coe_val v
    calc
      v % (n : ℤ) = (D.residue v).val := hv.symm
      _ = e.head.val := congrArg (fun x : Fin n => (x.val : ℤ)) hh.symm
      _ = (e.head.val : ℤ) % (n : ℤ) := by
        exact (Int.emod_eq_of_lt (Int.natCast_nonneg _)
          (by exact_mod_cast e.head.isLt)).symm
  have hright : (e.tail.val : ℤ) + (e.length.val : ℤ) ≡
      (e.head.val : ℤ) [ZMOD (n : ℤ)] := by
    have hnat : (e.tail.val + e.length.val) % n = e.head.val % n := by
      rw [e.tail_add_length_mod, Nat.mod_eq_of_lt e.head.isLt]
    exact_mod_cast hnat
  have hcancel := Int.ModEq.add_right_cancel' (e.length.val : ℤ)
    (hleft.trans hright.symm)
  apply Fin.ext
  apply Int.ofNat_inj.mp
  have hm := hcancel.eq
  rw [← D.residue_coe_val] at hm
  have htail : (e.tail.val : ℤ) % (n : ℤ) = e.tail.val :=
    Int.emod_eq_of_lt (Int.natCast_nonneg e.tail.val)
      (by exact_mod_cast e.tail.isLt)
  rw [htail] at hm
  exact hm.symm

theorem edgeFromLift_tail {u v : ℤ} (h : D.boundaryNaturalLift u v) :
    (D.edgeFromLift u v h).tail = D.residue u := by
  apply D.residue_tail_of_length
  · exact D.edgeFromLift_head h
  · exact D.edgeFromLift_length h

theorem edgeFromLift_naturalLift {u v : ℤ} (h : D.boundaryNaturalLift u v) :
    D.naturalLift (D.edgeFromLift u v h) u v := by
  constructor
  · exact (D.edgeFromLift_tail h).symm
  · rw [D.edgeFromLift_length h]
    ring

theorem boundaryNaturalLift_of_edge {e : Edge D.area} {u v : ℤ}
    (hh : e.head = D.residue v)
    (hlen : (e.length.val : ℤ) = v - u) : D.boundaryNaturalLift u v := by
  constructor
  · rw [Diagram.boundary]
    have hle : (e.length.val : ℤ) ≤ (D.area.area e.head : ℤ) := by
      exact_mod_cast e.length_le_area
    rw [hh] at hle
    linarith
  · have hpos : (0 : ℤ) < e.length.val := by
      exact_mod_cast e.length_pos
    linarith

/-- A head and length lift also gives the pre-existing edge-specific lift
predicate from `LiftCover`. -/
theorem naturalLift_of_head_length {e : Edge D.area} {u v : ℤ}
    (hh : e.head = D.residue v)
    (hlen : (e.length.val : ℤ) = v - u) : D.naturalLift e u v := by
  constructor
  · exact (D.residue_tail_of_length hh hlen).symm
  · rw [hlen]
    ring

theorem boundaryNaturalLift_iff_exists_edge {u v : ℤ} :
    D.boundaryNaturalLift u v ↔ ∃ e : Edge D.area,
      e.tail = D.residue u ∧ e.head = D.residue v ∧
        (e.length.val : ℤ) = v - u := by
  constructor
  · intro h
    refine ⟨D.edgeFromLift u v h, D.edgeFromLift_tail h,
      D.edgeFromLift_head h, D.edgeFromLift_length h⟩
  · rintro ⟨e, _, hh, hlen⟩
    exact D.boundaryNaturalLift_of_edge hh hlen

theorem edgeFromLift_mem_strict_iff {u v : ℤ} (h : D.boundaryNaturalLift u v) :
    D.edgeFromLift u v h ∈ D.strict ↔ D.strictAt v ∧ u = D.boundary v := by
  constructor
  · intro he
    refine ⟨⟨D.edgeFromLift u v h, he, D.edgeFromLift_head h⟩, ?_⟩
    have hc := D.strict_corner _ he
    have hcorner : ((D.edgeFromLift u v h).length.val : ℤ) =
        (D.area.area (D.residue v) : ℤ) := by
      rw [hc.1, D.edgeFromLift_head h]
    rw [D.edgeFromLift_length h] at hcorner
    rw [Diagram.boundary]
    linarith
  · rintro ⟨⟨e, he, hh⟩, hu⟩
    have hc := D.strict_corner e he
    have hlen : (e.length.val : ℤ) = v - u := by
      rw [hc.1, hh, hu, Diagram.boundary]
      ring
    have heq : e = D.edgeFromLift u v h := by
      apply Subtype.ext
      apply Prod.ext
      · exact hh.trans (D.edgeFromLift_head h).symm
      · apply Fin.ext
        apply Int.ofNat_inj.mp
        change (e.length.val : ℤ) = ((D.edgeFromLift u v h).length.val : ℤ)
        rw [D.edgeFromLift_length h]
        exact hlen
    simpa [heq] using he

end Diagram
end VerticalStripLLT.Circular
