import VerticalStripLLT.Circular.LiftedBoundary
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith

/-! Strict rows and their integer boundary gaps. -/

namespace VerticalStripLLT.Circular

open scoped Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

def strictAt (z : ℤ) : Prop :=
  ∃ e ∈ D.strict, e.head = D.residue z

theorem strictAt_add_period (z k : ℤ) :
    D.strictAt (z + (n : ℤ) * k) ↔ D.strictAt z := by
  constructor
  · rintro ⟨e, he, hh⟩
    exact ⟨e, he, hh.trans (D.residue_add_period z k)⟩
  · rintro ⟨e, he, hh⟩
    exact ⟨e, he, hh.trans (D.residue_add_period z k).symm⟩

theorem strictAt_boundary_lt {z : ℤ} (h : D.strictAt z) :
    D.boundary z < D.boundary (z + 1) := by
  rcases h with ⟨e, he, hh⟩
  have hc := D.strict_corner e he
  rw [Diagram.boundary, Diagram.boundary, D.residue_succ, ← hh]
  have harea : D.area.area e.head = e.length.val := hc.1.symm
  have hnext : D.area.area (D.area.next e.head) ≤ e.length.val := by
    exact hc.2.trans_eq hc.1.symm
  have hnext' :
      (D.area.area (D.area.next e.head) : ℤ) ≤ (e.length.val : ℤ) := by
    exact_mod_cast hnext
  have hpos : (0 : ℤ) < e.length.val := by exact_mod_cast e.length_pos
  lia

noncomputable def eastGap (z : ℤ) : ℤ :=
  D.boundary (z + 1) - D.boundary z - if D.strictAt z then 1 else 0

theorem eastGap_nonneg (z : ℤ) : 0 ≤ D.eastGap z := by
  classical
  unfold eastGap
  by_cases h : D.strictAt z
  · have hs := D.strictAt_boundary_lt h
    simp [h]
    lia
  · have hs := D.boundary_step_le z
    simp [h]
    lia

theorem strictAt_of_boundary_step
    (hsat : ∀ e, IsCorner e → e ∈ D.strict)
    {z : ℤ} (hpos : 0 < D.area.area (D.residue z))
    (hstep : D.boundary z < D.boundary (z + 1)) : D.strictAt z := by
  let e : Edge D.area :=
    ⟨(D.residue z, ⟨D.area.area (D.residue z), D.area.bound (D.residue z)⟩),
      ⟨hpos, le_rfl⟩⟩
  have hnext : D.area.area (D.area.next (D.residue z)) ≤
      D.area.area (D.residue z) := by
    rw [Diagram.boundary, Diagram.boundary, D.residue_succ] at hstep
    have hstep' :
        (D.area.area (D.area.next (D.residue z)) : ℤ) ≤
          (D.area.area (D.residue z) : ℤ) := by
      lia
    exact_mod_cast hstep'
  have hecorner : IsCorner e := by
    refine ⟨?_, ?_⟩
    · rfl
    · exact hnext
  have he : e ∈ D.strict := hsat e hecorner
  exact ⟨e, he, rfl⟩

private theorem residue_boundary_eq_tail {z : ℤ} {e : Edge D.area}
    (hh : e.head = D.residue z) (hlen : e.length.val = D.area.area e.head) :
    D.residue (D.boundary z) = e.tail := by
  have hsum : D.boundary z + (e.length.val : ℤ) = z := by
    rw [Diagram.boundary, hlen, hh]
    ring
  have hleft : D.boundary z + (e.length.val : ℤ) ≡
      (e.head.val : ℤ) [ZMOD (n : ℤ)] := by
    change (D.boundary z + (e.length.val : ℤ)) % (n : ℤ) =
      (e.head.val : ℤ) % (n : ℤ)
    rw [hsum]
    have hz := D.residue_coe_val z
    calc
      z % (n : ℤ) = (D.residue z).val := hz.symm
      _ = e.head.val := congrArg (fun v : Fin n => (v.val : ℤ)) hh.symm
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
  have hr : (e.tail.val : ℤ) % (n : ℤ) = e.tail.val :=
    Int.emod_eq_of_lt (Int.natCast_nonneg e.tail.val)
    (by exact_mod_cast e.tail.isLt)
  rw [hr] at hm
  exact hm

theorem selected_of_strictAt {z : ℤ} (h : D.strictAt z) :
    D.edgeData.selected ∅ (D.residue (D.boundary z)) (D.residue z) := by
  rcases h with ⟨e, he, hh⟩
  have hc := D.strict_corner e he
  have ht := residue_boundary_eq_tail D hh hc.1
  exact ⟨e, by simpa [Diagram.edgeData] using he, ht.symm, hh⟩

theorem strictAt_area_pos {z : ℤ} (h : D.strictAt z) :
    0 < D.area.area (D.residue z) := by
  rcases h with ⟨e, he, hh⟩
  have hc := D.strict_corner e he
  calc
    0 < e.length.val := e.length_pos
    _ = D.area.area e.head := hc.1
    _ = D.area.area (D.residue z) := congrArg D.area.area hh

theorem strictAt_boundary_lt_self {z : ℤ} (h : D.strictAt z) :
    D.boundary z < z := by
  have hp := D.strictAt_area_pos h
  rw [Diagram.boundary]
  lia

end Diagram
end VerticalStripLLT.Circular
