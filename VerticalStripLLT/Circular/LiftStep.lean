import VerticalStripLLT.Circular.Coloring
import VerticalStripLLT.Circular.EdgeBounds
import Mathlib.Data.Int.Init
import Mathlib.Tactic.Positivity

/-! Integer lifts of selected circular edges. -/

namespace VerticalStripLLT.Circular

namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- The residue of an integer position as a circular vertex. -/
def residue (z : ℤ) : Fin n :=
  ⟨z.natMod (n : ℤ), Int.natMod_lt (Nat.ne_of_gt D.area.positive)⟩

@[simp] theorem residue_coe_val (z : ℤ) :
    ((D.residue z).val : ℤ) = z % (n : ℤ) := by
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt D.area.positive)
  simp [residue, Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg z hn)]

/-- Adding an integral period does not change a residue. -/
theorem residue_add_period (z k : ℤ) :
    D.residue (z + (n : ℤ) * k) = D.residue z := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [D.residue_coe_val, D.residue_coe_val]
  simp [Int.add_emod]

/-- A lifted selected edge advances by its positive natural length. -/
def liftStep (A : Finset (Edge D.area)) (z w : ℤ) : Prop :=
  ∃ e ∈ D.strict ∪ A,
    D.residue z = e.tail ∧ w = z + (e.length.val : ℤ)

theorem liftStep_bounds {A : Finset (Edge D.area)} {z w : ℤ}
    (h : D.liftStep A z w) :
    0 < w - z ∧ w - z ≤ (n - 1 : ℕ) := by
  rcases h with ⟨e, _, _, hw⟩
  have hpos := e.length_pos
  have hlt := e.length_lt_n
  rw [hw, add_sub_cancel_left]
  constructor
  · exact_mod_cast hpos
  ·
    have hlen : e.length.val ≤ n - 1 := by
      lia
    exact_mod_cast hlen

theorem liftStep_selected {A : Finset (Edge D.area)} {z w : ℤ}
    (h : D.liftStep A z w) :
    D.edgeData.selected A (D.residue z) (D.residue w) := by
  rcases h with ⟨e, he, hz, hw⟩
  refine ⟨e, he, hz.symm, ?_⟩
  symm
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [D.residue_coe_val]
  have hz' := congrArg (fun v : Fin n => (v.val : ℤ)) hz
  rw [D.residue_coe_val] at hz'
  have hlenmod : (e.length.val : ℤ) % n = e.length.val :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast e.length_lt_n)
  rw [hw, Int.add_emod, hz', hlenmod]
  exact_mod_cast e.tail_add_length_mod

theorem liftStep_translate_iff {A : Finset (Edge D.area)} (z w k : ℤ) :
    D.liftStep A (z + (n : ℤ) * k) (w + (n : ℤ) * k) ↔
      D.liftStep A z w := by
  constructor
  · rintro ⟨e, he, hz, hw⟩
    refine ⟨e, he, ?_, ?_⟩
    · rw [D.residue_add_period] at hz
      exact hz
    · lia
  · rintro ⟨e, he, hz, hw⟩
    refine ⟨e, he, ?_, ?_⟩
    · rw [D.residue_add_period]
      exact hz
    · lia

end Diagram
end VerticalStripLLT.Circular
