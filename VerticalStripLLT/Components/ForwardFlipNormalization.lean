import VerticalStripLLT.Components.FlipTriangle
import VerticalStripLLT.Components.ShortEdges

/-!
# Canonical coordinates for flips in a forward diagram

Period translation preserves the full integer-cover relation, including all
possible intermediate integers. A forward flip has one common period offset
from its three canonical vertex ranks, so every cover test can be normalized.
-/

namespace VerticalStripLLT.Circular

variable {n : ℕ}

namespace Diagram

/-- Full integer covers are invariant under a simultaneous period translation. -/
theorem liftCover_translate_iff (D : Diagram n) (A : Finset (Edge D.area))
    (x y k : ℤ) :
    D.liftCover A (x + (n : ℤ) * k) (y + (n : ℤ) * k) ↔ D.liftCover A x y := by
  have hr (u v : ℤ) := reflTransGen_translate_iff (D.liftStep A) ((n : ℤ) * k) u v
    (fun a b => D.liftStep_translate_iff a b k)
  constructor
  · rintro ⟨hxy, hreach, hcover⟩
    refine ⟨by lia, (hr x y).mp hreach, ?_⟩
    intro z hxz hzy hpaths
    exact hcover (z + (n : ℤ) * k) (by lia) (by lia)
      ⟨(hr x z).mpr hpaths.1, (hr z y).mpr hpaths.2⟩
  · rintro ⟨hxy, hreach, hcover⟩
    refine ⟨by lia, (hr x y).mpr hreach, ?_⟩
    intro z hxz hzy hpaths
    apply hcover (z - (n : ℤ) * k) (by lia) (by lia)
    constructor
    · apply (hr x (z - (n : ℤ) * k)).mp
      simpa only [sub_add_cancel] using hpaths.1
    · apply (hr (z - (n : ℤ) * k) y).mp
      simpa only [sub_add_cancel] using hpaths.2

end Diagram

namespace DirectedFlipWitness

variable {D : Diagram n} {θ η : Orientation D}

/-- The natural forward shorts order the three canonical vertex ranks. -/
theorem canonical_triple_order (w : DirectedFlipWitness D θ η)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) :
    w.eab.tail < w.eab.head ∧ w.eab.head < w.ebc.head := by
  refine ⟨hforward w.eab, ?_⟩
  rw [w.short_head_tail]
  exact hforward w.ebc

/-- All three coordinates of a forward witness have the same period offset. -/
theorem exists_common_period_of_forward (w : DirectedFlipWitness D θ η)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) :
    ∃ t : ℤ, w.a = (w.eab.tail.val : ℤ) + (n : ℤ) * t ∧
      w.b = (w.eab.head.val : ℤ) + (n : ℤ) * t ∧
      w.c = (w.ebc.head.val : ℤ) + (n : ℤ) * t := by
  have hres : D.residue w.a = D.residue (w.eab.tail.val : ℤ) := by
    rw [Orientation.residue_intCast_eq]
    exact w.ab_lift.1
  obtain ⟨t, ha⟩ := D.residue_eq_exists_period hres
  have hab := w.ab_lift.2
  have hbc := w.bc_lift.2
  have hab0 := (D.naturalLift_of_tail_lt_head w.eab (hforward w.eab)).2
  have hbc0 := (D.naturalLift_of_tail_lt_head w.ebc (hforward w.ebc)).2
  rw [← w.short_head_tail] at hbc0
  refine ⟨t, ha, ?_, ?_⟩ <;> lia

/-- Normalize all six cover tests to the canonical ranks, retaining the same flip. -/
noncomputable def normalizeForward (w : DirectedFlipWitness D θ η)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) : DirectedFlipWitness D θ η := by
  let t := Classical.choose (w.exists_common_period_of_forward hforward)
  have ht := Classical.choose_spec (w.exists_common_period_of_forward hforward)
  have ha : w.a = (w.eab.tail.val : ℤ) + (n : ℤ) * t := ht.1
  have hb : w.b = (w.eab.head.val : ℤ) + (n : ℤ) * t := ht.2.1
  have hc : w.c = (w.ebc.head.val : ℤ) + (n : ℤ) * t := ht.2.2
  refine {
    a := (w.eab.tail.val : ℤ)
    b := (w.eab.head.val : ℤ)
    c := (w.ebc.head.val : ℤ)
    cyclicWindow := ?_
    eab := w.eab
    ebc := w.ebc
    eab_normal := w.eab_normal
    ebc_normal := w.ebc_normal
    ab_lift := D.naturalLift_of_tail_lt_head w.eab (hforward w.eab)
    bc_lift := ?_
    source_ab := ?_
    source_ac := ?_
    source_not_bc := ?_
    target_ac := ?_
    target_bc := ?_
    target_not_ab := ?_
    agree_elsewhere := w.agree_elsewhere
  }
  · have hord := w.canonical_triple_order hforward
    have hij : (w.eab.tail.val : ℤ) < (w.eab.head.val : ℤ) := by
      exact_mod_cast hord.1
    have hjk : (w.eab.head.val : ℤ) < (w.ebc.head.val : ℤ) := by
      exact_mod_cast hord.2
    have hk : (w.ebc.head.val : ℤ) < (n : ℤ) := by exact_mod_cast w.ebc.head.isLt
    have hi : (0 : ℤ) ≤ w.eab.tail.val := Int.natCast_nonneg _
    exact ⟨hij, hjk, by lia⟩
  · rw [w.short_head_tail]
    exact D.naturalLift_of_tail_lt_head w.ebc (hforward w.ebc)
  · apply (D.liftCover_translate_iff θ.val _ _ t).mp
    rw [← ha, ← hb]
    exact w.source_ab
  · apply (D.liftCover_translate_iff θ.val _ _ t).mp
    rw [← ha, ← hc]
    exact w.source_ac
  · intro h
    apply w.source_not_bc
    rw [hb, hc]
    exact (D.liftCover_translate_iff θ.val _ _ t).mpr h
  · apply (D.liftCover_translate_iff η.val _ _ t).mp
    rw [← ha, ← hc]
    exact w.target_ac
  · apply (D.liftCover_translate_iff η.val _ _ t).mp
    rw [← hb, ← hc]
    exact w.target_bc
  · intro h
    apply w.target_not_ab
    rw [ha, hb]
    exact (D.liftCover_translate_iff η.val _ _ t).mpr h

@[simp]
theorem normalizeForward_a (w : DirectedFlipWitness D θ η)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) :
    (w.normalizeForward hforward).a = (w.eab.tail.val : ℤ) := rfl

@[simp]
theorem normalizeForward_b (w : DirectedFlipWitness D θ η)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) :
    (w.normalizeForward hforward).b = (w.eab.head.val : ℤ) := rfl

@[simp]
theorem normalizeForward_c (w : DirectedFlipWitness D θ η)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) :
    (w.normalizeForward hforward).c = (w.ebc.head.val : ℤ) := rfl

@[simp]
theorem normalizeForward_eab (w : DirectedFlipWitness D θ η)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) :
    (w.normalizeForward hforward).eab = w.eab := rfl

@[simp]
theorem normalizeForward_ebc (w : DirectedFlipWitness D θ η)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) :
    (w.normalizeForward hforward).ebc = w.ebc := rfl

end DirectedFlipWitness

end VerticalStripLLT.Circular
