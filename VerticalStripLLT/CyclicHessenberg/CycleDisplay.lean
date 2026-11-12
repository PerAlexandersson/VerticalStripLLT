import VerticalStripLLT.CyclicHessenberg.BoundaryOrder
import VerticalStripLLT.OrientationNatural

/-! Canonical cycle displays include singleton blocks and retain their actual rotation direction. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V : Type*} [LinearOrder V]

def cycleSourceWord (B : List (V × List V)) : List V :=
  B.flatMap (fun b => b.1 :: b.2)

def cycleTargetWord (B : List (V × List V)) : List V :=
  B.flatMap (fun b => b.2 ++ [b.1])

theorem cycleSourceWord_perm_target (B : List (V × List V)) :
    (cycleSourceWord B).Perm (cycleTargetWord B) := by
  induction B with
  | nil => exact List.Perm.refl []
  | cons b B ih =>
    change (([b.1] ++ b.2) ++ cycleSourceWord B).Perm
      ((b.2 ++ [b.1]) ++ cycleTargetWord B)
    exact List.perm_append_comm.append ih

/-- Each block starts at its maximum; block roots strictly decrease.
Singleton blocks are represented by an empty tail. -/
structure CycleDisplay (S : Finset V) where
  blocks : List (V × List V)
  source_order : IsOrder S (cycleSourceWord blocks)
  root_max : ∀ b ∈ blocks, ∀ a ∈ b.2, a < b.1
  roots_desc : blocks.Pairwise (fun b c => c.1 < b.1)

namespace CycleDisplay

@[ext] theorem ext {S : Finset V} {D E : CycleDisplay S}
    (h : D.blocks = E.blocks) : D = E := by
  cases D
  cases E
  cases h
  rfl

def source {S : Finset V} (D : CycleDisplay S) : Order S :=
  ⟨cycleSourceWord D.blocks, D.source_order⟩

def target {S : Finset V} (D : CycleDisplay S) : Order S :=
  ⟨cycleTargetWord D.blocks, D.source_order.perm (cycleSourceWord_perm_target D.blocks)⟩

/-- Read the source position and then the target vertex. -/
def toPerm {S : Finset V} (D : CycleDisplay S) : Equiv.Perm S :=
  (orderEquiv D.source).symm.trans (orderEquiv D.target)

theorem toPerm_apply_source {S : Finset V} (D : CycleDisplay S) (i : Fin S.card) :
    D.toPerm (orderEquiv D.source i) = orderEquiv D.target i := by
  simp only [toPerm, Equiv.trans_apply, Equiv.symm_apply_apply]

def count {S : Finset V} (D : CycleDisplay S) : ℕ := D.blocks.length

def blockSize (b : V × List V) : ℕ+ := ⟨b.2.length + 1, Nat.zero_lt_succ _⟩

noncomputable def shape {S : Finset V} (D : CycleDisplay S) : ℕ+ →₀ ℕ :=
  (D.blocks.map fun b => Finsupp.single (blockSize b) 1).sum

noncomputable def elementaryMonomial {S : Finset V} (D : CycleDisplay S) : NEExpansion :=
  (D.blocks.map fun b => natElementary (blockSize b)).prod

private theorem blocks_length_le (B : List (V × List V)) :
    B.length ≤ (cycleSourceWord B).length := by
  induction B with
  | nil => simp [cycleSourceWord]
  | cons b B ih =>
    change B.length + 1 ≤ (b.1 :: b.2 ++ cycleSourceWord B).length
    simp only [List.length_cons, List.length_append]
    lia

theorem count_le_card {S : Finset V} (D : CycleDisplay S) : D.count ≤ S.card := by
  rw [← D.source_order.length]
  exact blocks_length_le D.blocks

theorem root_mem {S : Finset V} (D : CycleDisplay S) {b : V × List V}
    (hb : b ∈ D.blocks) : b.1 ∈ S := by
  apply (D.source_order.mem_iff b.1).mp
  exact List.mem_flatMap.mpr ⟨b, hb, List.mem_cons_self⟩

theorem tail_mem {S : Finset V} (D : CycleDisplay S) {b : V × List V}
    (hb : b ∈ D.blocks) {a : V} (ha : a ∈ b.2) : a ∈ S := by
  apply (D.source_order.mem_iff a).mp
  exact List.mem_flatMap.mpr ⟨b, hb, List.mem_cons_of_mem _ ha⟩

theorem first_root_max {S : Finset V} (D : CycleDisplay S) (r : V) (t : List V)
    (B : List (V × List V)) (hB : D.blocks = (r, t) :: B) : ∀ a ∈ S, a ≤ r := by
  intro a ha
  have hamem := (D.source_order.mem_iff a).mpr ha
  obtain ⟨b, hb, hab⟩ := List.mem_flatMap.mp hamem
  have hroot := D.root_max b hb
  rw [hB] at hb
  have hdesc := D.roots_desc
  rw [hB, List.pairwise_cons] at hdesc
  rcases List.mem_cons.mp hb with rfl | hb
  · rcases List.mem_cons.mp hab with rfl | hab
    · exact le_rfl
    · exact (hroot a hab).le
  · have hbr : b.1 < r := hdesc.1 b hb
    rcases List.mem_cons.mp hab with rfl | hab
    · exact hbr.le
    · exact (lt_trans (hroot a hab) hbr).le

def empty : CycleDisplay (∅ : Finset V) where
  blocks := []
  source_order := by simp [IsOrder, cycleSourceWord]
  root_max := by simp
  roots_desc := by simp

@[simp] theorem empty_count : (empty (V := V)).count = 0 := rfl

end CycleDisplay

end VerticalStripLLT.CyclicHessenberg
