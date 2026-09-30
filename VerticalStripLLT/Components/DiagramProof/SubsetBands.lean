import VerticalStripLLT.Components.DiagramProof.FiniteSubsetPaths

/-!
# Connectivity of finite subset bands

The vertices are the subsets of a fixed finite ambient set whose cardinalities
lie in a prescribed interval.  A move inserts or deletes one element while
remaining in that interval.
-/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V : Type*} [DecidableEq V]

/-- Subsets of `J` whose cardinality is in the closed band `[L, U]`. -/
def SubsetBand (J : Finset V) (L U : ℕ) :=
  {S : Finset V // S ⊆ J ∧ L ≤ S.card ∧ S.card ≤ U}

/-- Insert or delete one element, with both endpoints already in the band. -/
def subsetBandStep {J : Finset V} {L U : ℕ}
    (S T : SubsetBand J L U) : Prop :=
  (∃ x, x ∉ S.val ∧ T.val = insert x S.val) ∨
    ∃ x, x ∈ S.val ∧ T.val = S.val.erase x

private theorem subsetBand_insert {J : Finset V} {L U : ℕ}
    (S : SubsetBand J L U) (x : V) (hxJ : x ∈ J) (hx : x ∉ S.val)
    (hcard : S.val.card < U) :
    ∃ T : SubsetBand J L U, subsetBandStep S T ∧ T.val = insert x S.val := by
  let T : SubsetBand J L U := ⟨insert x S.val, by
    refine ⟨?_, ?_, ?_⟩
    · exact Finset.insert_subset hxJ S.property.1
    · rw [Finset.card_insert_of_notMem hx]
      exact Nat.le_succ_of_le S.property.2.1
    · rw [Finset.card_insert_of_notMem hx]
      exact Nat.succ_le_of_lt hcard⟩
  exact ⟨T, Or.inl ⟨x, hx, rfl⟩, rfl⟩

private theorem subsetBand_erase {J : Finset V} {L U : ℕ}
    (S : SubsetBand J L U) (x : V) (hx : x ∈ S.val)
    (hcard : L < S.val.card) :
    ∃ T : SubsetBand J L U, subsetBandStep S T ∧ T.val = S.val.erase x := by
  let T : SubsetBand J L U := ⟨S.val.erase x, by
    refine ⟨?_, ?_, ?_⟩
    · exact (Finset.erase_subset x S.val).trans S.property.1
    · have h := Finset.card_erase_add_one hx
      lia
    · have h := Finset.card_erase_add_one hx
      have hU := S.property.2.2
      lia⟩
  exact ⟨T, Or.inr ⟨x, hx, rfl⟩, rfl⟩

private theorem subsetBandStep_symm {J : Finset V} {L U : ℕ}
    {S T : SubsetBand J L U} (h : subsetBandStep S T) : subsetBandStep T S := by
  rcases h with ⟨x, hx, hT⟩ | ⟨x, hx, hT⟩
  · refine Or.inr ⟨x, ?_, ?_⟩
    · rw [hT]
      exact Finset.mem_insert_self x S.val
    · rw [hT]
      exact (Finset.erase_insert hx).symm
  · refine Or.inl ⟨x, ?_, ?_⟩
    · rw [hT]
      exact Finset.notMem_erase x S.val
    · rw [hT]
      exact (Finset.insert_erase hx).symm

private theorem subsetBand_reachable_symm {J : Finset V} {L U : ℕ}
    {S T : SubsetBand J L U}
    (h : Relation.ReflTransGen subsetBandStep S T) :
    Relation.ReflTransGen subsetBandStep T S := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.head (subsetBandStep_symm hs)

/-- Delete down to a specified lower-bound subset without leaving the band. -/
private theorem subsetBand_reachable_down {J : Finset V} {L U : ℕ}
    (S T : SubsetBand J L U) (hsub : T.val ⊆ S.val) (hT : T.val.card = L) :
    Relation.ReflTransGen subsetBandStep S T := by
  generalize hN : (S.val \ T.val).card = N
  induction N using Nat.strong_induction_on generalizing S with
  | h N ih =>
    by_cases hzero : N = 0
    · have hdiff : S.val \ T.val = ∅ :=
        Finset.card_eq_zero.mp (by simpa [hN] using hzero)
      have hST : S.val ⊆ T.val := by
        intro x hx
        by_contra hxt
        have : x ∈ S.val \ T.val := Finset.mem_sdiff.mpr ⟨hx, hxt⟩
        rw [hdiff] at this
        simp at this
      have hEq : S.val = T.val := Finset.Subset.antisymm hST hsub
      exact (Subtype.ext hEq) ▸ Relation.ReflTransGen.refl
    · have hpos : 0 < (S.val \ T.val).card := by
        rw [hN]
        exact Nat.pos_of_ne_zero hzero
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      have hxS : x ∈ S.val := (Finset.mem_sdiff.mp hx).1
      have hxT : x ∉ T.val := (Finset.mem_sdiff.mp hx).2
      have hsum := Finset.card_sdiff_add_card_eq_card hsub
      have hcard : L < S.val.card := by
        rw [hT] at hsum
        lia
      obtain ⟨S', hsstep, hS'⟩ := subsetBand_erase S x hxS hcard
      have hsub' : T.val ⊆ S'.val := by
        rw [hS']
        intro y hy
        exact Finset.mem_erase.mpr ⟨fun h => hxT (h ▸ hy), hsub hy⟩
      have hdiff : S'.val \ T.val = (S.val \ T.val).erase x := by
        rw [hS']
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        grind
      have hmeasure : (S'.val \ T.val).card < N := by
        rw [hdiff, ← hN]
        exact Finset.card_erase_lt_of_mem hx
      exact (Relation.ReflTransGen.single hsstep).trans
        (ih _ hmeasure S' hsub' rfl)

/-- At the lower level, exchange an unwanted element by add-then-delete. -/
private theorem subsetBand_reachable_lower {J : Finset V} {L U : ℕ}
    (hLU : L < U) (S T : SubsetBand J L U)
    (hS : S.val.card = L) (hT : T.val.card = L) :
    Relation.ReflTransGen subsetBandStep S T := by
  generalize hN : (S.val \ T.val).card = N
  induction N using Nat.strong_induction_on generalizing S with
  | h N ih =>
    by_cases hzero : N = 0
    · have hdiff : S.val \ T.val = ∅ :=
        Finset.card_eq_zero.mp (by simpa [hN] using hzero)
      have hsub : S.val ⊆ T.val := by
        intro x hx
        by_contra hxt
        have : x ∈ S.val \ T.val := Finset.mem_sdiff.mpr ⟨hx, hxt⟩
        rw [hdiff] at this
        simp at this
      have hEq : S.val = T.val :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hS, hT])
      exact (Subtype.ext hEq) ▸ Relation.ReflTransGen.refl
    · have hpos : 0 < (S.val \ T.val).card := by
        rw [hN]
        exact Nat.pos_of_ne_zero hzero
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
      have haS : a ∈ S.val := (Finset.mem_sdiff.mp ha).1
      have haT : a ∉ T.val := (Finset.mem_sdiff.mp ha).2
      have hdiffCard : (S.val \ T.val).card = (T.val \ S.val).card :=
        Finset.card_sdiff_eq_card_sdiff_iff.mpr (by rw [hS, hT])
      have hotherPos : 0 < (T.val \ S.val).card := by
        rw [← hdiffCard]
        exact hpos
      obtain ⟨b, hb⟩ := Finset.card_pos.mp hotherPos
      have hbT : b ∈ T.val := (Finset.mem_sdiff.mp hb).1
      have hbS : b ∉ S.val := (Finset.mem_sdiff.mp hb).2
      obtain ⟨M, hmstep, hM⟩ :=
        subsetBand_insert S b (T.property.1 hbT) hbS (by rw [hS]; exact hLU)
      have haM : a ∈ M.val := by
        rw [hM]
        exact Finset.mem_insert_of_mem haS
      obtain ⟨S', hsstep, hS'⟩ := subsetBand_erase M a haM (by
        rw [hM, Finset.card_insert_of_notMem hbS, hS]
        exact Nat.lt_succ_self L)
      have hS'card : S'.val.card = L := by
        rw [hS', hM]
        have hcard := Finset.card_erase_add_one haM
        rw [hM, Finset.card_insert_of_notMem hbS, hS] at hcard
        lia
      have hdiff : S'.val \ T.val = (S.val \ T.val).erase a := by
        rw [hS', hM]
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        grind
      have hmeasure : (S'.val \ T.val).card < N := by
        rw [hdiff, ← hN]
        exact Finset.card_erase_lt_of_mem ha
      exact (Relation.ReflTransGen.single hmstep).trans
        ((Relation.ReflTransGen.single hsstep).trans
          (ih _ hmeasure S' hS'card rfl))

/-- A nontrivial finite subset band is connected by single insertions and deletions. -/
theorem subsetBand_connected_of_lt {J : Finset V} {L U : ℕ}
    (hLU : L < U) (S T : SubsetBand J L U) :
    Relation.ReflTransGen subsetBandStep S T := by
  obtain ⟨S0, hS0sub, hS0card⟩ := Finset.exists_subset_card_eq S.property.2.1
  obtain ⟨T0, hT0sub, hT0card⟩ := Finset.exists_subset_card_eq T.property.2.1
  let S' : SubsetBand J L U := ⟨S0, hS0sub.trans S.property.1,
    hS0card.ge, hS0card.le.trans hLU.le⟩
  let T' : SubsetBand J L U := ⟨T0, hT0sub.trans T.property.1,
    hT0card.ge, hT0card.le.trans hLU.le⟩
  have hSS' : Relation.ReflTransGen subsetBandStep S S' := by
    apply subsetBand_reachable_down S S'
    · change S0 ⊆ S.val
      exact hS0sub
    · change S0.card = L
      exact hS0card
  have hS'T' : Relation.ReflTransGen subsetBandStep S' T' := by
    apply subsetBand_reachable_lower hLU S' T'
    · change S0.card = L
      exact hS0card
    · change T0.card = L
      exact hT0card
  have hTT' : Relation.ReflTransGen subsetBandStep T T' := by
    apply subsetBand_reachable_down T T'
    · change T0 ⊆ T.val
      exact hT0sub
    · change T0.card = L
      exact hT0card
  exact hSS'.trans (hS'T'.trans (subsetBand_reachable_symm hTT'))

/-- The zero-level band has only the empty subset. -/
theorem subsetBand_connected_zero {J : Finset V} {L U : ℕ}
    (hU : U = 0) (S T : SubsetBand J L U) :
    Relation.ReflTransGen subsetBandStep S T := by
  have hScard : S.val.card = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa only [hU] using S.property.2.2
  have hTcard : T.val.card = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa only [hU] using T.property.2.2
  have hS : S.val = ∅ := Finset.card_eq_zero.mp hScard
  have hT : T.val = ∅ := Finset.card_eq_zero.mp hTcard
  exact (Subtype.ext (hS.trans hT.symm)) ▸ Relation.ReflTransGen.refl

/-- The top-level band has only the ambient subset. -/
theorem subsetBand_connected_top {J : Finset V} {L U : ℕ}
    (hL : L = J.card) (S T : SubsetBand J L U) :
    Relation.ReflTransGen subsetBandStep S T := by
  have hScard : S.val.card = J.card := by
    apply le_antisymm (Finset.card_le_card S.property.1)
    simpa only [hL] using S.property.2.1
  have hTcard : T.val.card = J.card := by
    apply le_antisymm (Finset.card_le_card T.property.1)
    simpa only [hL] using T.property.2.1
  have hS : S.val = J :=
    Finset.eq_of_subset_of_card_le S.property.1 (by rw [hScard])
  have hT : T.val = J :=
    Finset.eq_of_subset_of_card_le T.property.1 (by rw [hTcard])
  exact (Subtype.ext (hS.trans hT.symm)) ▸ Relation.ReflTransGen.refl

/-- The subset band connects in the nontrivial and singleton cases. -/
theorem subsetBand_connected {J : Finset V} {L U : ℕ}
    (h : L < U ∨ (L = U ∧ (L = 0 ∨ L = J.card)))
    (S T : SubsetBand J L U) : Relation.ReflTransGen subsetBandStep S T := by
  rcases h with hLU | ⟨hLU, hL | hL⟩
  · exact subsetBand_connected_of_lt hLU S T
  · exact subsetBand_connected_zero (hLU ▸ hL) S T
  · exact subsetBand_connected_top hL S T

end VerticalStripLLT.Circular.DiagramProof
