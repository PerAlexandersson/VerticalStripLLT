import VerticalStripLLT.Components.WordProof.HRVPartition
import VerticalStripLLT.Components.OrderedPartitions

/-! Adapters from top-first ordered blocks to actual forward HRV fibers. -/

namespace VerticalStripLLT.Components

open Classical
open OrderedPartitions

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Reversing the relation in `IsCompatible` exposes the cross condition used
by concatenated compatible words. -/
theorem cross_of_reverse_compatible {R : V → V → Prop}
    {S : Finset V} {bs : List (Finset V)}
    (h : IsCompatible (fun x y => R y x) S bs) :
    bs.Pairwise (fun U W => ∀ u ∈ U, ∀ w ∈ W, ¬ R w u) := by
  induction bs generalizing S with
  | nil => simp
  | cons U bs ih =>
      obtain ⟨hU, hbs⟩ := h
      have hcross :
          ∀ W ∈ bs, ∀ u ∈ U, ∀ w ∈ W, ¬ R w u := by
        intro W hW u hu w hw hwu
        have hWsub : W ⊆ S \ U := hbs.blocks_subset W hW
        have hwSU : w ∈ S \ U := hWsub hw
        have hwS : w ∈ S := (Finset.mem_sdiff.mp hwSU).1
        have hUclosed : UpClosed (fun x y => R y x) S U :=
          ((mem_topBlocks (fun x y => R y x) S U).mp hU).2.2
        have hwU : w ∈ U := hUclosed hu hwS hwu
        exact (Finset.mem_sdiff.mp hwSU).2 hwU
      rw [List.pairwise_cons]
      exact ⟨hcross, ih hbs⟩

end

namespace OrderedBlockHRV

open Circular

variable {n k : ℕ} {D : Circular.Diagram n}

private theorem exists_get_mem_of_compatible
    {bs : List (Finset (Fin n))}
    (R : Fin n → Fin n → Prop)
    (hpart : IsCompatible (fun x y : Fin n => R y x)
      (Finset.univ : Finset (Fin n)) bs)
    (v : Fin n) :
    ∃ i : Fin bs.length, v ∈ bs.get i := by
  obtain ⟨U, hU, hvU⟩ := (IsCompatible.mem_iff hpart v).mp (Finset.mem_univ v)
  obtain ⟨j, hj, hjU⟩ := List.getElem_of_mem hU
  refine ⟨⟨j, hj⟩, ?_⟩
  rw [List.get_eq_getElem, hjU]
  exact hvU

private theorem get_mem_unique
    {bs : List (Finset (Fin n))}
    (hdisj : bs.Pairwise Disjoint) {i j : Fin bs.length} {v : Fin n}
    (hi : v ∈ bs.get i) (hj : v ∈ bs.get j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hd : Disjoint (bs.get i) (bs.get j) := hdisj.rel_get_of_lt hij
    exact (Finset.disjoint_left.mp hd) hi hj
  · have hd : Disjoint (bs.get j) (bs.get i) := hdisj.rel_get_of_lt hji
    exact (Finset.disjoint_left.mp hd) hj hi

/-- A reverse-compatible partition on all vertices has its blocks equal to
the HRV fibers, once roots and unique induced sinks are supplied. -/
theorem hrv_fiber_eq_get_of_reverse_compatible
    (θ : Circular.Orientation D)
    (hforward : ∀ e : Circular.Edge D.area, e.tail < e.head)
    (bs : List (Finset (Fin n)))
    (hpart : IsCompatible
      (fun x y : Fin n => D.edgeData.selected θ.val y x)
      (Finset.univ : Finset (Fin n)) bs)
    (root : Fin bs.length → Fin n)
    (hroot_mem : ∀ i, root i ∈ bs.get i)
    (hmax : ∀ i v, v ∈ bs.get i → v ≤ root i)
    (hroot_desc : StrictAnti root)
    (hunique : ∀ i v,
      sinkOn (D.edgeData.selected θ.val) (bs.get i) v ↔ v = root i)
    (i : Fin bs.length) :
    Finset.univ.filter (fun v => θ.hrv v = root i) = bs.get i := by
  let owner : Fin n → Fin bs.length := fun v =>
    Classical.choose (exists_get_mem_of_compatible
      (D.edgeData.selected θ.val) hpart v)
  have howner_mem (v : Fin n) : v ∈ bs.get (owner v) := by
    exact Classical.choose_spec (exists_get_mem_of_compatible
      (D.edgeData.selected θ.val) hpart v)
  have hdisj : bs.Pairwise Disjoint := hpart.pairwise_disjoint
  have howner_iff (j : Fin bs.length) (v : Fin n) :
      v ∈ bs.get j ↔ owner v = j := by
    constructor
    · intro hv
      exact get_mem_unique hdisj (howner_mem v) hv
    · intro h
      rw [← h]
      exact howner_mem v
  have hcross := cross_of_reverse_compatible hpart
  have hcross_get {j l : Fin bs.length} (hjl : j < l) :
      ∀ u ∈ bs.get j, ∀ v ∈ bs.get l, ¬ D.edgeData.selected θ.val v u :=
    hcross.rel_get_of_lt hjl
  have howner_mono : ∀ ⦃u v : Fin n⦄,
      D.edgeData.selected θ.val u v → owner u ≤ owner v := by
    intro u v huv
    by_contra hnot
    have hlt : owner v < owner u := lt_of_not_ge hnot
    exact hcross_get hlt v (howner_mem v) u (howner_mem u) huv
  exact hrv_fiber_eq_partition_block θ hforward
    (fun j => bs.get j) root owner hroot_mem hmax howner_mem howner_iff
    hroot_desc howner_mono hunique i

end OrderedBlockHRV

end VerticalStripLLT.Components
