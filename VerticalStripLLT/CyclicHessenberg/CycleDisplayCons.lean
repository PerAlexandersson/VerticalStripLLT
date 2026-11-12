import VerticalStripLLT.CyclicHessenberg.CycleDisplay
import VerticalStripLLT.CyclicHessenberg.KernelSupport

set_option autoImplicit false

/-! Add the maximal-root block to a cycle display. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V : Type*} [LinearOrder V]

namespace CycleDisplay

/-- Prepend a root block and retain a display of the complementary support. -/
def cons (S U : Finset V) (r : V) (hUS : U ⊆ S) (hr : r ∈ U)
    (hmax : ∀ a ∈ S, a ≤ r) (σ : Order (U.erase r))
    (D : CycleDisplay (S \ U)) : CycleDisplay S where
  blocks := (r, σ.val) :: D.blocks
  source_order := by
    have hd : Disjoint U (S \ U) := Finset.disjoint_sdiff
    have hp := (rootPrefix_isOrder U r hr σ).append D.source_order hd
    rw [Finset.union_sdiff_of_subset hUS] at hp
    change IsOrder S ((r :: σ.val) ++ cycleSourceWord D.blocks)
    exact hp
  root_max := by
    intro b hb a ha
    rcases List.mem_cons.mp hb with hb | hb
    · cases hb
      have haErase : a ∈ U.erase r := (σ.property.mem_iff a).mp ha
      have haU : a ∈ U := (Finset.mem_erase.mp haErase).2
      have haNe : a ≠ r := (Finset.mem_erase.mp haErase).1
      exact lt_of_le_of_ne (hmax a (hUS haU)) haNe
    · exact D.root_max b hb a ha
  roots_desc := by
    rw [List.pairwise_cons]
    constructor
    · intro b hb
      have hbRest : b.1 ∈ S \ U := D.root_mem hb
      have hbS := (Finset.mem_sdiff.mp hbRest).1
      have hbNotU := (Finset.mem_sdiff.mp hbRest).2
      have hbNe : b.1 ≠ r := by
        intro heq
        apply hbNotU
        rw [heq]
        exact hr
      exact lt_of_le_of_ne (hmax b.1 hbS) hbNe
    · exact D.roots_desc

@[simp] theorem cons_blocks (S U : Finset V) (r : V) (hUS : U ⊆ S)
    (hr : r ∈ U) (hmax : ∀ a ∈ S, a ≤ r) (σ : Order (U.erase r))
    (D : CycleDisplay (S \ U)) :
    (cons S U r hUS hr hmax σ D).blocks = (r, σ.val) :: D.blocks := rfl

@[simp] theorem cons_source_val (S U : Finset V) (r : V) (hUS : U ⊆ S)
    (hr : r ∈ U) (hmax : ∀ a ∈ S, a ≤ r) (σ : Order (U.erase r))
    (D : CycleDisplay (S \ U)) :
    (cons S U r hUS hr hmax σ D).source.val =
      (r :: σ.val) ++ D.source.val := rfl

@[simp] theorem cons_target_val (S U : Finset V) (r : V) (hUS : U ⊆ S)
    (hr : r ∈ U) (hmax : ∀ a ∈ S, a ≤ r) (σ : Order (U.erase r))
    (D : CycleDisplay (S \ U)) :
    (cons S U r hUS hr hmax σ D).target.val =
      (σ.val ++ [r]) ++ D.target.val := rfl

@[simp] theorem cons_count (S U : Finset V) (r : V) (hUS : U ⊆ S)
    (hr : r ∈ U) (hmax : ∀ a ∈ S, a ≤ r) (σ : Order (U.erase r))
    (D : CycleDisplay (S \ U)) :
    (cons S U r hUS hr hmax σ D).count = 1 + D.count := by
  simp [count, cons, Nat.add_comm]

theorem cons_first_block_toFinset (S U : Finset V) (r : V) (hUS : U ⊆ S)
    (hr : r ∈ U) (hmax : ∀ a ∈ S, a ≤ r) (σ : Order (U.erase r))
    (D : CycleDisplay (S \ U)) :
    (r :: σ.val).toFinset = U := (rootPrefix_isOrder U r hr σ).2

end CycleDisplay

end VerticalStripLLT.CyclicHessenberg
