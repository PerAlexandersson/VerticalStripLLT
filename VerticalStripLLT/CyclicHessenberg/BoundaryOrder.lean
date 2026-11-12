import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.NodupEquivFin

/-! Orders of finite named supports. Deletion retains the original vertex names. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {V : Type*} [LinearOrder V]

/-- A list contains each member of the support exactly once. -/
def IsOrder (S : Finset V) (l : List V) : Prop :=
  l.Nodup ∧ l.toFinset = S

/-- Boundary orders retain the ambient vertex names. -/
abbrev Order (S : Finset V) := {l : List V // IsOrder S l}

namespace IsOrder

theorem perm {S : Finset V} {l t : List V} (h : IsOrder S l) (hp : l.Perm t) :
    IsOrder S t :=
  ⟨hp.nodup_iff.mp h.1, (List.toFinset_eq_of_perm _ _ hp).symm.trans h.2⟩

theorem mem_iff {S : Finset V} {l : List V} (h : IsOrder S l) (v : V) :
    v ∈ l ↔ v ∈ S := by
  rw [← h.2, List.mem_toFinset]

theorem length {S : Finset V} {l : List V} (h : IsOrder S l) :
    l.length = S.card := by
  rw [← h.2, List.toFinset_card_of_nodup h.1]

theorem append {A B : Finset V} {l t : List V}
    (hl : IsOrder A l) (ht : IsOrder B t) (hd : Disjoint A B) :
    IsOrder (A ∪ B) (l ++ t) := by
  refine ⟨List.nodup_append'.mpr ⟨hl.1, ht.1, ?_⟩, ?_⟩
  · intro v hv hw
    exact Finset.disjoint_left.mp hd ((hl.mem_iff v).mp hv) ((ht.mem_iff v).mp hw)
  · simp [List.toFinset_append, hl.2, ht.2]

end IsOrder

/-- A fixed prefix cancels from the order predicate on a disjoint union. -/
theorem isOrder_append_left_iff {A B : Finset V} {p l : List V}
    (hp : IsOrder A p) (hd : Disjoint A B) :
    IsOrder (A ∪ B) (p ++ l) ↔ IsOrder B l := by
  constructor
  · intro h
    obtain ⟨hnp, hnl, hdis⟩ := List.nodup_append'.mp h.1
    refine ⟨hnl, Finset.ext fun v => ?_⟩
    simp only [List.mem_toFinset]
    constructor
    · intro hv
      have huv := (h.mem_iff v).mp (List.mem_append_right p hv)
      rcases Finset.mem_union.mp huv with ha | hb
      · exact False.elim (hdis ((hp.mem_iff v).mpr ha) hv)
      · exact hb
    · intro hv
      have huv := (h.mem_iff v).mpr (Finset.mem_union_right A hv)
      rcases List.mem_append.mp huv with ha | hb
      · exact False.elim (Finset.disjoint_left.mp hd ((hp.mem_iff v).mp ha) hv)
      · exact hb
  · exact fun h => hp.append h hd

/-- A fixed suffix cancels from the order predicate on a disjoint union. -/
theorem isOrder_append_right_iff {A B : Finset V} {l s : List V}
    (hs : IsOrder B s) (hd : Disjoint A B) :
    IsOrder (A ∪ B) (l ++ s) ↔ IsOrder A l := by
  have hcomm : IsOrder (A ∪ B) (l ++ s) ↔ IsOrder (B ∪ A) (s ++ l) := by
    constructor <;> intro h
    · simpa only [Finset.union_comm] using h.perm (List.perm_append_comm l s)
    · simpa only [Finset.union_comm] using h.perm (List.perm_append_comm s l)
  exact hcomm.trans (isOrder_append_left_iff hs hd.symm)

/-- Enumerate orders by the permutations of the increasing list. -/
instance orderFintype (S : Finset V) : Fintype (Order S) := by
  classical
  refine Fintype.subtype (S.sort.permutations.toFinset) ?_
  intro l
  simp only [List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h
    exact ⟨h.nodup_iff.mpr (S.sort_nodup _),
      (List.toFinset_eq_of_perm _ _ h).trans (S.sort_toFinset _)⟩
  · intro h
    exact List.perm_of_nodup_nodup_toFinset_eq h.1 (S.sort_nodup _)
      (h.2.trans (S.sort_toFinset _).symm)

/-- The increasing boundary order. -/
def increasingOrder (S : Finset V) : Order S :=
  ⟨S.sort, S.sort_nodup _, S.sort_toFinset _⟩

/-- The decreasing boundary order. -/
def decreasingOrder (S : Finset V) : Order S :=
  ⟨S.sort (· ≥ ·), S.sort_nodup _, S.sort_toFinset _⟩

/-- Concatenate orders of disjoint supports. -/
def appendOrder {A B : Finset V} (hd : Disjoint A B)
    (l : Order A) (t : Order B) : Order (A ∪ B) :=
  ⟨l.val ++ t.val, l.property.append t.property hd⟩

@[simp] theorem length_order {S : Finset V} (l : Order S) :
    l.val.length = S.card := l.property.length

@[simp] theorem mem_order {S : Finset V} (l : Order S) (v : V) :
    v ∈ l.val ↔ v ∈ S := l.property.mem_iff v

@[simp] theorem appendOrder_val {A B : Finset V} (hd : Disjoint A B)
    (l : Order A) (t : Order B) :
    (appendOrder hd l t).val = l.val ++ t.val := rfl

@[simp] theorem order_empty_val (l : Order (∅ : Finset V)) : l.val = [] := by
  have h := length_order l
  simpa using h

instance orderEmptySubsingleton : Subsingleton (Order (∅ : Finset V)) :=
  ⟨fun l t => Subtype.ext ((order_empty_val l).trans (order_empty_val t).symm)⟩

/-- Swap the displayed adjacent positions, retaining both exterior lists. -/
theorem isOrder_swapAdjacent {S : Finset V} (ρ σ : List V) (a b : V)
    (h : IsOrder S (ρ ++ [a, b] ++ σ)) : IsOrder S (ρ ++ [b, a] ++ σ) := by
  apply h.perm
  exact ((List.Perm.swap b a []).append_left ρ).append_right σ

end VerticalStripLLT.CyclicHessenberg
