import VerticalStripLLT.CyclicHessenberg.BoundaryOrder
import Mathlib.Data.List.InsertIdx
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-! Inserting and erasing one named vertex in finite boundary orders. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators List

variable {V : Type*} [LinearOrder V]

omit [LinearOrder V] in
private theorem insertIdx_eq_take_cons_drop (l : List V) (i : ℕ) (a : V)
    (hi : i ≤ l.length) : l.insertIdx i a = l.take i ++ a :: l.drop i := by
  induction l generalizing i with
  | nil =>
    have : i = 0 := by simpa using hi
    subst i
    simp
  | cons b l ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hi' : i ≤ l.length := Nat.le_of_succ_le_succ hi
      simp only [List.insertIdx_succ_cons, List.take_succ_cons,
        List.drop_succ_cons]
      rw [ih i hi']
      simp

/-- Insert `a` into an order at a specified position. -/
def insertOrder {S : Finset V} (a : V) (ha : a ∉ S)
    (σ : Order S) (i : Fin (S.card + 1)) : Order (insert a S) := by
  classical
  have haσ : a ∉ σ.val := by
    intro h
    exact ha ((mem_order σ a).mp h)
  have hi : (i : ℕ) ≤ σ.val.length := by
    rw [length_order]
    exact Nat.le_of_lt_succ i.isLt
  have hperm : σ.val.insertIdx i a ~ a :: σ.val := by
    apply List.perm_insertIdx
    exact hi
  have hbase : IsOrder (insert a S) (a :: σ.val) := by
    constructor
    · exact List.nodup_cons.mpr ⟨haσ, σ.property.1⟩
    · simp [σ.property.2]
  exact ⟨σ.val.insertIdx i a, hbase.perm hperm.symm⟩

/-- The list of an inserted order is the usual `take`/`drop` insertion. -/
theorem insertOrder_val {S : Finset V} (a : V) (ha : a ∉ S)
    (σ : Order S) (i : Fin (S.card + 1)) :
    (insertOrder a ha σ i).val = σ.val.take i ++ a :: σ.val.drop i := by
  apply insertIdx_eq_take_cons_drop
  rw [length_order]
  exact Nat.le_of_lt_succ i.isLt

private def eraseOrder {S : Finset V} (a : V) (ha : a ∉ S)
    (τ : Order (insert a S)) : Order S := by
  classical
  refine ⟨τ.val.eraseIdx (τ.val.idxOf a), ?_⟩
  let n := τ.val.idxOf a
  have hmem : a ∈ τ.val := (mem_order τ a).mpr (Finset.mem_insert_self a S)
  have hn : n < τ.val.length := List.idxOf_lt_length_iff.mpr hmem
  have hget : τ.val.get ⟨n, hn⟩ = a := List.idxOf_get hn
  have hperm : a :: τ.val.eraseIdx n ~ τ.val := by
    simpa only [show τ.val[n] = a from hget] using
      (List.getElem_cons_eraseIdx_perm hn)
  have hnd : (a :: τ.val.eraseIdx n).Nodup := hperm.nodup_iff.mpr τ.property.1
  obtain ⟨haerase, hnderase⟩ := List.nodup_cons.mp hnd
  refine ⟨hnderase, ?_⟩
  apply Finset.ext
  intro v
  simp only [List.mem_toFinset]
  constructor
  · intro hv
    have hvt : v ∈ τ.val := hperm.mem_iff.mp (List.mem_cons.mpr (Or.inr hv))
    have hvS := (mem_order τ v).mp hvt
    rcases Finset.mem_insert.mp hvS with hEq | hvS
    · subst v
      exact (haerase hv).elim
    · exact hvS
  · intro hv
    have hvt : v ∈ τ.val := (mem_order τ v).mpr (Finset.mem_insert_of_mem hv)
    have hv' : v ∈ a :: τ.val.eraseIdx n := hperm.mem_iff.mpr hvt
    rcases List.mem_cons.mp hv' with hEq | hvErase
    · exact False.elim (ha (hEq ▸ hv))
    · exact hvErase

private def insertPosition {S : Finset V} (a : V) (ha : a ∉ S)
    (τ : Order (insert a S)) : Fin (S.card + 1) := by
  classical
  refine ⟨τ.val.idxOf a, ?_⟩
  have hmem : a ∈ τ.val := (mem_order τ a).mpr (Finset.mem_insert_self a S)
  have hn := List.idxOf_lt_length_iff.mpr hmem
  simpa [length_order, Finset.card_insert_of_notMem ha] using hn

/-- Insertion positions and orders of `S` are equivalent to orders of `insert a S`. -/
def insertionEquiv {S : Finset V} (a : V) (ha : a ∉ S) :
    Order S × Fin (S.card + 1) ≃ Order (insert a S) where
  toFun p := insertOrder a ha p.1 p.2
  invFun τ := (eraseOrder a ha τ, insertPosition a ha τ)
  left_inv := by
    intro p
    rcases p with ⟨σ, i⟩
    have hi : (i : ℕ) ≤ σ.val.length := by
      rw [length_order]
      exact Nat.le_of_lt_succ i.isLt
    have hlen : i.val < (σ.val.insertIdx i a).length := by
      rw [List.length_insertIdx_of_le_length hi]
      exact Nat.lt_succ_of_le hi
    have hget : (σ.val.insertIdx i a).get ⟨i.val, hlen⟩ = a :=
      List.get_insertIdx_self σ.val a i.val hi
    have hidx : (σ.val.insertIdx i a).idxOf a = i.val := by
      have h := List.get_idxOf (insertOrder a ha σ i).property.1 ⟨i.val, hlen⟩
      change (σ.val.insertIdx i a).idxOf
        ((σ.val.insertIdx i a).get ⟨i.val, hlen⟩) = i.val at h
      rw [hget] at h
      exact h
    apply Prod.ext
    · apply Subtype.ext
      change (σ.val.insertIdx i a).eraseIdx
        ((σ.val.insertIdx i a).idxOf a) = σ.val
      rw [hidx]
      simp
    · apply Fin.ext
      exact hidx
  right_inv := by
    intro τ
    have hmem : a ∈ τ.val := (mem_order τ a).mpr (Finset.mem_insert_self a S)
    have hn : τ.val.idxOf a < τ.val.length := List.idxOf_lt_length_iff.mpr hmem
    have hget : τ.val.get ⟨τ.val.idxOf a, hn⟩ = a := List.idxOf_get hn
    apply Subtype.ext
    change (τ.val.eraseIdx (τ.val.idxOf a)).insertIdx
      (τ.val.idxOf a) a = τ.val
    simpa only [show τ.val[τ.val.idxOf a] = a from hget] using
      (List.insertIdx_eraseIdx_getElem hn)

/-- Reindex the finite sum over an order and an insertion position by the inserted order. -/
theorem sum_insertOrder {S : Finset V} (a : V) (ha : a ∉ S) {R : Type*}
    [AddCommMonoid R] (f : Order (insert a S) → R) :
    (∑ σ : Order S, ∑ i : Fin (S.card + 1), f (insertOrder a ha σ i)) =
      ∑ τ : Order (insert a S), f τ := by
  classical
  exact (Fintype.sum_prod_type (fun p : Order S × Fin (S.card + 1) =>
    f (insertOrder a ha p.1 p.2))).symm.trans (Equiv.sum_comp (insertionEquiv a ha) f)

end VerticalStripLLT.CyclicHessenberg
