import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn

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
    · simpa only [Finset.union_comm] using h.perm List.perm_append_comm
    · simpa only [Finset.union_comm] using h.perm List.perm_append_comm
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

/-- Read a boundary order as a bijection from its positions to the named support. -/
def orderEquiv {S : Finset V} (l : Order S) : Fin S.card ≃ S :=
  (finCongr (length_order l).symm).trans
    ((List.Nodup.getEquiv l.val l.property.1).trans
      (Equiv.subtypeEquivRight (fun v => l.property.mem_iff v)))

@[simp] theorem orderEquiv_apply {S : Finset V} (l : Order S) (i : Fin S.card) :
    (orderEquiv l i).val = l.val.get (Fin.cast (length_order l).symm i) := rfl

/-- Recover the list of a bijection, in position order. -/
def orderOfEquiv {S : Finset V} (e : Fin S.card ≃ S) : Order S := by
  refine ⟨List.ofFn (fun i => (e i).val), ?_, ?_⟩
  · rw [List.nodup_ofFn]
    intro i j hij
    exact e.injective (Subtype.ext hij)
  · apply Finset.ext
    intro v
    simp only [List.mem_toFinset, List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hv
      exact ⟨e.symm ⟨v, hv⟩, congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)⟩

@[simp] theorem orderOfEquiv_orderEquiv {S : Finset V} (l : Order S) :
    orderOfEquiv (orderEquiv l) = l := by
  apply Subtype.ext
  change List.ofFn (fun i => l.val.get (Fin.cast (length_order l).symm i)) = l.val
  rw [← List.ofFn_congr (length_order l) l.val.get, List.ofFn_get]

@[simp] theorem orderEquiv_orderOfEquiv {S : Finset V} (e : Fin S.card ≃ S) :
    orderEquiv (orderOfEquiv e) = e := by
  apply Equiv.ext
  intro i
  apply Subtype.ext
  simp [orderOfEquiv]

/-- Orders and bijections enumerate exactly the same finite boundary states. -/
def ordersEquiv (S : Finset V) : Order S ≃ (Fin S.card ≃ S) where
  toFun := orderEquiv
  invFun := orderOfEquiv
  left_inv := orderOfEquiv_orderEquiv
  right_inv := orderEquiv_orderOfEquiv

@[simp] theorem appendOrder_val {A B : Finset V} (hd : Disjoint A B)
    (l : Order A) (t : Order B) :
    (appendOrder hd l t).val = l.val ++ t.val := rfl

@[simp] theorem order_empty_val (l : Order (∅ : Finset V)) : l.val = [] := by
  have h := length_order l
  exact List.length_eq_zero_iff.mp h

instance orderEmptySubsingleton : Subsingleton (Order (∅ : Finset V)) :=
  ⟨fun l t => Subtype.ext ((order_empty_val l).trans (order_empty_val t).symm)⟩

/-- Swap the displayed adjacent positions, retaining both exterior lists. -/
theorem isOrder_swapAdjacent {S : Finset V} (ρ σ : List V) (a b : V)
    (h : IsOrder S (ρ ++ [a, b] ++ σ)) : IsOrder S (ρ ++ [b, a] ++ σ) := by
  apply h.perm
  exact ((List.Perm.swap b a []).append_left ρ).append_right σ

/-- Exchange positions `i,i+1`; an out-of-range exchange is the identity. -/
def swapAdjacentList : ℕ → List V → List V
  | 0, a :: b :: l => b :: a :: l
  | i + 1, a :: l => a :: swapAdjacentList i l
  | _, l => l

omit [LinearOrder V] in
theorem swapAdjacentList_perm (i : ℕ) (l : List V) : l.Perm (swapAdjacentList i l) := by
  induction i generalizing l with
  | zero =>
    cases l with
    | nil => exact List.Perm.refl _
    | cons a l =>
      cases l with
      | nil => exact List.Perm.refl _
      | cons b l => exact List.Perm.swap b a l
  | succ i ih =>
    cases l with
    | nil => exact List.Perm.refl _
    | cons a l => exact (ih l).cons a

omit [LinearOrder V] in
@[simp] theorem swapAdjacentList_involutive (i : ℕ) (l : List V) :
    swapAdjacentList i (swapAdjacentList i l) = l := by
  induction i generalizing l with
  | zero => cases l with
    | nil => rfl
    | cons a l => cases l <;> rfl
  | succ i ih => cases l with
    | nil => rfl
    | cons a l => simp only [swapAdjacentList, ih]

omit [LinearOrder V] in
theorem swapAdjacentList_context (ρ σ : List V) (a b : V) :
    swapAdjacentList ρ.length (ρ ++ [a, b] ++ σ) = ρ ++ [b, a] ++ σ := by
  induction ρ with
  | nil => rfl
  | cons c ρ ih =>
    simpa only [List.length_cons, List.cons_append, swapAdjacentList] using
      (congrArg (List.cons c) ih)

/-- Adjacent exchange on the finite type of orders. -/
def swapAdjacent {S : Finset V} (i : ℕ) (l : Order S) : Order S :=
  ⟨swapAdjacentList i l.val, l.property.perm (swapAdjacentList_perm i l.val)⟩

@[simp] theorem swapAdjacent_involutive {S : Finset V} (i : ℕ) (l : Order S) :
    swapAdjacent i (swapAdjacent i l) = l := by
  apply Subtype.ext
  exact swapAdjacentList_involutive i l.val

/-- Whether the entries at the displayed adjacent positions are increasing. -/
def IncreasingAt : ℕ → List V → Prop
  | 0, a :: b :: _ => a < b
  | i + 1, _ :: l => IncreasingAt i l
  | _, _ => False

instance increasingAtDecidable (i : ℕ) (l : List V) : Decidable (IncreasingAt i l) := by
  induction i generalizing l with
  | zero => cases l with
    | nil => exact inferInstanceAs (Decidable False)
    | cons a l => cases l with
      | nil => exact inferInstanceAs (Decidable False)
      | cons b l => exact inferInstanceAs (Decidable (a < b))
  | succ i ih => cases l with
    | nil => exact inferInstanceAs (Decidable False)
    | cons a l => exact ih l

theorem increasingAt_context (ρ σ : List V) (a b : V) :
    IncreasingAt ρ.length (ρ ++ [a, b] ++ σ) ↔ a < b := by
  induction ρ with
  | nil => rfl
  | cons c ρ ih => exact ih

omit [LinearOrder V] in
/-- Every valid adjacent position has a prefix/pair/suffix decomposition. -/
theorem adjacent_context (i : ℕ) (l : List V) (hi : i + 1 < l.length) :
    ∃ (ρ σ : List V) (a b : V), ρ.length = i ∧ l = ρ ++ [a, b] ++ σ := by
  induction i generalizing l with
  | zero =>
    cases l with
    | nil => simp at hi
    | cons a l => cases l with
      | nil => simp at hi
      | cons b l => exact ⟨[], l, a, b, rfl, rfl⟩
  | succ i ih =>
    cases l with
    | nil => simp at hi
    | cons c l =>
      obtain ⟨ρ, σ, a, b, hρ, hl⟩ := ih l (Nat.lt_of_succ_lt_succ hi)
      exact ⟨c :: ρ, σ, a, b, congrArg Nat.succ hρ, by rw [hl]; rfl⟩

theorem increasingAt_swapAdjacent {S : Finset V} (i : ℕ) (hi : i + 1 < S.card)
    (l : Order S) : IncreasingAt i (swapAdjacent i l).val ↔ ¬ IncreasingAt i l.val := by
  obtain ⟨ρ, σ, a, b, hρ, hl⟩ := adjacent_context i l.val (by simpa using hi)
  have hnd : (ρ ++ [a, b] ++ σ).Nodup := hl ▸ l.property.1
  have hab : a ≠ b := by
    have h := (List.nodup_append'.mp hnd).1
    have h' := (List.nodup_append'.mp h).2.1
    simpa using h'
  change IncreasingAt i (swapAdjacentList i l.val) ↔ ¬ IncreasingAt i l.val
  rw [hl, ← hρ, swapAdjacentList_context, increasingAt_context, increasingAt_context]
  constructor
  · exact fun h h' => (lt_asymm h h')
  · intro h
    exact lt_of_le_of_ne (le_of_not_gt h) hab.symm

end VerticalStripLLT.CyclicHessenberg
