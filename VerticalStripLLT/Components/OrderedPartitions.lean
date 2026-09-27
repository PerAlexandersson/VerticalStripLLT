import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# Compatible ordered partitions and their top-block recursion

Blocks are listed from highest to lowest level. Thus the first block is an
up-closed subset of the remaining vertex set. The empty set has exactly one
partition, the empty list, with sign one. No acyclicity is assumed here.
-/

namespace VerticalStripLLT.Components.OrderedPartitions

open scoped BigOperators Classical

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Upward closure is relative to the current induced vertex set. -/
def UpClosed (R : V → V → Prop) (S U : Finset V) : Prop :=
  ∀ ⦃x y⦄, x ∈ U → y ∈ S → R x y → y ∈ U

/-- All possible highest blocks of a compatible ordered partition of `S`. -/
def topBlocks (R : V → V → Prop) (S : Finset V) : Finset (Finset V) :=
  S.powerset.filter fun U => U.Nonempty ∧ UpClosed R S U

@[simp]
theorem mem_topBlocks (R : V → V → Prop) (S U : Finset V) :
    U ∈ topBlocks R S ↔ U ⊆ S ∧ U.Nonempty ∧ UpClosed R S U := by
  simp [topBlocks]

@[simp]
theorem topBlocks_empty (R : V → V → Prop) : topBlocks R ∅ = ∅ := by
  ext U
  simp only [mem_topBlocks, Finset.subset_empty, Finset.notMem_empty, iff_false]
  rintro ⟨rfl, h, _⟩
  exact Finset.not_nonempty_empty h

theorem card_sdiff_lt_of_mem_topBlocks (R : V → V → Prop) {S U : Finset V}
    (hU : U ∈ topBlocks R S) : (S \ U).card < S.card := by
  obtain ⟨hsub, hne, _⟩ := (mem_topBlocks R S U).mp hU
  have hsum := Finset.card_sdiff_add_card_eq_card hsub
  have hpos := hne.card_pos
  lia

/-- A top-first compatible ordered partition. Each step removes its nonempty
highest block; the empty list is permitted precisely on the empty vertex set. -/
def IsCompatible (R : V → V → Prop) : Finset V → List (Finset V) → Prop
  | S, [] => S = ∅
  | S, U :: bs => U ∈ topBlocks R S ∧ IsCompatible R (S \ U) bs

/-- The actual finite set of all compatible ordered partitions. -/
def partitions (R : V → V → Prop) (S : Finset V) : Finset (List (Finset V)) :=
  if S = ∅ then {[]} else
    (topBlocks R S).attach.biUnion fun U =>
      (partitions R (S \ U.val)).image (List.cons U.val)
termination_by S.card
decreasing_by exact card_sdiff_lt_of_mem_topBlocks R U.property

@[simp]
theorem partitions_empty (R : V → V → Prop) : partitions R ∅ = {[]} := by
  rw [partitions, ite_eq_left rfl]

theorem partitions_of_nonempty (R : V → V → Prop) {S : Finset V}
    (hS : S.Nonempty) :
    partitions R S = (topBlocks R S).attach.biUnion fun U =>
      (partitions R (S \ U.val)).image (List.cons U.val) := by
  rw [partitions, ite_eq_right hS.ne_empty]

/-- Completeness of the finite enumeration. -/
@[simp]
theorem mem_partitions (R : V → V → Prop) (S : Finset V) (bs : List (Finset V)) :
    bs ∈ partitions R S ↔ IsCompatible R S bs := by
  induction bs generalizing S with
  | nil =>
    by_cases hS : S = ∅
    · subst S
      simp [IsCompatible]
    · rw [partitions, ite_eq_right hS]
      simp [IsCompatible, hS]
  | cons U bs ih =>
    by_cases hS : S = ∅
    · subst S
      simp [IsCompatible]
    · rw [partitions, ite_eq_right hS]
      simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Finset.mem_image,
        List.cons.injEq]
      constructor
      · rintro ⟨W, cs, hcs, hWU, hcsbs⟩
        subst U
        subst cs
        exact ⟨W.property, (ih _).mp hcs⟩
      · rintro ⟨hU, hbs⟩
        exact ⟨⟨U, hU⟩, bs, (ih _).mpr hbs, rfl, rfl⟩

theorem IsCompatible.blocks_subset {R : V → V → Prop} {S : Finset V}
    {bs : List (Finset V)} (h : IsCompatible R S bs) :
    ∀ U ∈ bs, U ⊆ S := by
  induction bs generalizing S with
  | nil => simp
  | cons U bs ih =>
    obtain ⟨hU, hbs⟩ := h
    intro W hW
    rcases List.mem_cons.mp hW with rfl | hW
    · exact ((mem_topBlocks R S W).mp hU).1
    · exact (ih hbs W hW).trans Finset.sdiff_subset

theorem IsCompatible.blocks_nonempty {R : V → V → Prop} {S : Finset V}
    {bs : List (Finset V)} (h : IsCompatible R S bs) :
    ∀ U ∈ bs, U.Nonempty := by
  induction bs generalizing S with
  | nil => simp
  | cons U bs ih =>
    obtain ⟨hU, hbs⟩ := h
    intro W hW
    rcases List.mem_cons.mp hW with rfl | hW
    · exact ((mem_topBlocks R S W).mp hU).2.1
    · exact ih hbs W hW

theorem IsCompatible.pairwise_disjoint {R : V → V → Prop} {S : Finset V}
    {bs : List (Finset V)} (h : IsCompatible R S bs) :
    bs.Pairwise Disjoint := by
  induction bs generalizing S with
  | nil => simp
  | cons U bs ih =>
    obtain ⟨hU, hbs⟩ := h
    rw [List.pairwise_cons]
    refine ⟨?_, ih hbs⟩
    intro W hW
    apply Finset.disjoint_left.mpr
    intro x hxU hxW
    exact (Finset.mem_sdiff.mp (hbs.blocks_subset W hW hxW)).2 hxU

theorem IsCompatible.mem_iff {R : V → V → Prop} {S : Finset V}
    {bs : List (Finset V)} (h : IsCompatible R S bs) (v : V) :
    v ∈ S ↔ ∃ U ∈ bs, v ∈ U := by
  induction bs generalizing S with
  | nil =>
    change S = ∅ at h
    simp [h]
  | cons U bs ih =>
    obtain ⟨hU, hbs⟩ := h
    have hsub := ((mem_topBlocks R S U).mp hU).1
    constructor
    · intro hv
      by_cases hvU : v ∈ U
      · exact ⟨U, List.mem_cons_self, hvU⟩
      · obtain ⟨W, hW, hvW⟩ := (ih hbs).mp (Finset.mem_sdiff.mpr ⟨hv, hvU⟩)
        exact ⟨W, List.mem_cons_of_mem U hW, hvW⟩
    · rintro ⟨W, hW, hvW⟩
      rcases List.mem_cons.mp hW with rfl | hW
      · exact hsub hvW
      · exact (Finset.mem_sdiff.mp ((ih hbs).mpr ⟨W, hW, hvW⟩)).1

theorem IsCompatible.length_le_card {R : V → V → Prop} {S : Finset V}
    {bs : List (Finset V)} (h : IsCompatible R S bs) : bs.length ≤ S.card := by
  induction bs generalizing S with
  | nil => simp
  | cons U bs ih =>
    have hlt := card_sdiff_lt_of_mem_topBlocks R h.1
    have hle := ih h.2
    simp only [List.length_cons]
    lia

/-- The signed ordered-partition enumerator in Lemma A. -/
def signedSum (R : V → V → Prop) (S : Finset V) : ℤ :=
  ∑ bs ∈ partitions R S, (-1 : ℤ) ^ bs.length

@[simp]
theorem signedSum_empty (R : V → V → Prop) : signedSum R ∅ = 1 := by
  simp [signedSum]

/-- Peeling off the top block changes the sign exactly once. -/
theorem signedSum_top_recursion (R : V → V → Prop) {S : Finset V}
    (hS : S.Nonempty) :
    signedSum R S = -∑ U ∈ topBlocks R S, signedSum R (S \ U) := by
  have hdisjoint : Set.PairwiseDisjoint ((topBlocks R S).attach : Set {U // U ∈ topBlocks R S})
      (fun U => (partitions R (S \ U.val)).image (List.cons U.val)) := by
    intro U _ W _ hne
    apply Finset.disjoint_left.mpr
    intro bs hU hW
    obtain ⟨us, _, hus⟩ := Finset.mem_image.mp hU
    obtain ⟨ws, _, hws⟩ := Finset.mem_image.mp hW
    have hUW : U.val = W.val := (List.cons.inj (hus.trans hws.symm)).1
    exact hne (Subtype.ext hUW)
  unfold signedSum
  rw [partitions_of_nonempty R hS, Finset.sum_biUnion hdisjoint]
  have hterm (U : {U // U ∈ topBlocks R S}) :
      (∑ bs ∈ (partitions R (S \ U.val)).image (List.cons U.val),
        (-1 : ℤ) ^ bs.length) =
      -(∑ bs ∈ partitions R (S \ U.val), (-1 : ℤ) ^ bs.length) := by
    rw [Finset.sum_image]
    · simp only [List.length_cons, pow_succ, mul_neg_one, Finset.sum_neg_distrib]
    · intro a _ b _ hab
      exact List.cons_injective hab
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib]
  exact congrArg Neg.neg (Finset.sum_attach (topBlocks R S)
    (fun U => ∑ bs ∈ partitions R (S \ U), (-1 : ℤ) ^ bs.length))

/-- Heads of edges in the induced relation on `S`. -/
def edgeHeads (R : V → V → Prop) (S : Finset V) : Finset V :=
  S.filter fun y => ∃ x ∈ S, R x y

/-- The induced relation has no edges, including no loops. -/
def Edgeless (R : V → V → Prop) (S : Finset V) : Prop :=
  ∀ ⦃x y⦄, x ∈ S → y ∈ S → ¬ R x y

/-- The subsets contributing after the DAG induction are exactly those
containing every edge head. This characterization itself needs no acyclicity. -/
theorem upClosed_edgeless_sdiff_iff (R : V → V → Prop) (S U : Finset V)
    (hsub : U ⊆ S) :
    UpClosed R S U ∧ Edgeless R (S \ U) ↔ edgeHeads R S ⊆ U := by
  constructor
  · rintro ⟨hup, hempty⟩ y hy
    obtain ⟨hyS, x, hxS, hxy⟩ := Finset.mem_filter.mp hy
    by_contra hyU
    have hxU : x ∉ U := fun hx => hyU (hup hx hyS hxy)
    exact hempty (Finset.mem_sdiff.mpr ⟨hxS, hxU⟩)
      (Finset.mem_sdiff.mpr ⟨hyS, hyU⟩) hxy
  · intro hheads
    constructor
    · intro x y hxU hyS hxy
      exact hheads (Finset.mem_filter.mpr ⟨hyS, x, hsub hxU, hxy⟩)
    · intro x y hx hy hxy
      exact (Finset.mem_sdiff.mp hy).2
        (hheads (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hy).1,
          x, (Finset.mem_sdiff.mp hx).1, hxy⟩))

end

end VerticalStripLLT.Components.OrderedPartitions
