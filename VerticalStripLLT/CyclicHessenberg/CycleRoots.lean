import VerticalStripLLT.CyclicHessenberg.OrbitAction

set_option autoImplicit false

/-! Maximal representatives of the cycles of a finite permutation. -/

namespace VerticalStripLLT.CyclicHessenberg

open Equiv.Perm

variable {α : Type*} [LinearOrder α] [Fintype α] [DecidableEq α]

/-- The maximal element of each permutation cycle. -/
noncomputable def cycleRoots (p : Equiv.Perm α) : Finset α := by
  classical
  exact Finset.univ.filter fun r => ∀ x, p.SameCycle r x → x ≤ r

theorem mem_cycleRoots_iff (p : Equiv.Perm α) (r : α) :
    r ∈ cycleRoots p ↔ ∀ x, p.SameCycle r x → x ≤ r := by
  classical
  simp [cycleRoots]

/-- Two maximal representatives of the same cycle must coincide. -/
theorem cycleRoots_sameCycle_eq (p : Equiv.Perm α) {r s : α}
    (hr : r ∈ cycleRoots p) (hs : s ∈ cycleRoots p)
    (hrs : p.SameCycle r s) : r = s := by
  have hmaxR := (mem_cycleRoots_iff p r).mp hr
  have hmaxS := (mem_cycleRoots_iff p s).mp hs
  exact le_antisymm (hmaxS r hrs.symm) (hmaxR s hrs)

/-- Every point has a unique maximal representative in its cycle. -/
theorem existsUnique_cycleRoot (p : Equiv.Perm α) (x : α) :
    ∃! r, r ∈ cycleRoots p ∧ p.SameCycle r x := by
  classical
  let C : Finset α := Finset.univ.filter fun y => p.SameCycle y x
  have hC : C.Nonempty := by
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, SameCycle.rfl⟩⟩
  let r := C.max' hC
  have hrC : r ∈ C := by
    exact Finset.max'_mem C hC
  have hrx : p.SameCycle r x := (Finset.mem_filter.mp hrC).2
  have hmax : ∀ y, p.SameCycle r y → y ≤ r := by
    intro y hry
    have hyx : p.SameCycle y x := hry.symm.trans hrx
    have hyC : y ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyx⟩
    have hle := Finset.le_max' C y hyC
    simpa [r] using hle
  refine ⟨r, ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmax⟩, hrx⟩, ?_⟩
  intro s hs
  exact cycleRoots_sameCycle_eq p hs.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmax⟩)
    (hs.2.trans hrx.symm)

/-- Every other point on the corrected orbit list lies strictly below its cycle root. -/
theorem correctedOrbitList_other_lt_root (p : Equiv.Perm α) (r x : α)
    (hr : r ∈ cycleRoots p) (hx : x ∈ correctedOrbitList p r) (hne : x ≠ r) :
    x < r := by
  have hcycle := (mem_correctedOrbitList_iff p r x).mp hx
  have hle := (mem_cycleRoots_iff p r).mp hr x hcycle
  exact lt_of_le_of_ne hle hne

/-- Corrected orbit lists of distinct cycle roots are disjoint. -/
theorem correctedOrbitList_disjoint_of_cycleRoots_ne (p : Equiv.Perm α)
    {r s : α} (hr : r ∈ cycleRoots p) (hs : s ∈ cycleRoots p) (hrs : r ≠ s) :
    List.Disjoint (correctedOrbitList p r) (correctedOrbitList p s) := by
  rw [List.disjoint_left]
  intro x hx hy
  have hrx := (mem_correctedOrbitList_iff p r x).mp hx
  have hsx := (mem_correctedOrbitList_iff p s x).mp hy
  exact hrs (cycleRoots_sameCycle_eq p hr hs (hrx.trans hsx.symm))

end VerticalStripLLT.CyclicHessenberg
