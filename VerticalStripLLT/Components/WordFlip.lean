import VerticalStripLLT.Components.WordCover

/-! Actual circular flip witnesses supplied by compatible contiguous triples. -/

namespace VerticalStripLLT.Components

open Circular

variable {n : ℕ} {D : Diagram n}

private theorem fullWord_acb_to_bac (ρ σ : List (Fin n)) {a b c : Fin n}
    (hw : fullWord (ρ ++ [a, c, b] ++ σ)) :
    fullWord (ρ ++ [b, a, c] ++ σ) := by
  have hp : ([a, c, b] : List (Fin n)).Perm [b, a, c] :=
    List.perm_append_singleton b [a, c]
  exact (fullWord_perm_iff
    (List.Perm.append_right σ (List.Perm.append_left ρ hp))).mp hw

private theorem wordCompatible_middle (R : Fin n → Fin n → Prop)
    (ρ w σ : List (Fin n)) (hw : wordCompatible R (ρ ++ w ++ σ)) :
    wordCompatible R w := by
  simp only [wordCompatible, List.pairwise_append] at hw ⊢
  grind

/-- The exchanged orientations and their compatible words determine all actual
lifted-cover fields of a directed flip. No component-membership or cover
hypotheses are required. The retained long edge may be strict. -/
noncomputable def directedFlipWitness_of_compatible_triples
    (θ η : Circular.Orientation D) (ρ σ : List (Fin n))
    {a b c : Fin n} (hab : a < b) (hbc : b < c)
    (hw : fullWord (ρ ++ [a, c, b] ++ σ))
    (hsource : wordCompatible (D.edgeData.selected θ.val) (ρ ++ [a, c, b] ++ σ))
    (htarget : wordCompatible (D.edgeData.selected η.val) (ρ ++ [b, a, c] ++ σ))
    (eab ebc eac : Edge D.area)
    (heab : eab ∈ D.edgeData.normalEdges) (hebc : ebc ∈ D.edgeData.normalEdges)
    (habLift : D.naturalLift eab (a.val : ℤ) (b.val : ℤ))
    (hbcLift : D.naturalLift ebc (b.val : ℤ) (c.val : ℤ))
    (hacLift : D.naturalLift eac (a.val : ℤ) (c.val : ℤ))
    (habMem : eab ∈ θ.val) (hacMem : eac ∈ D.strict ∪ θ.val)
    (hswap : η.val = insert ebc (θ.val.erase eab)) : DirectedFlipWitness D θ η := by
  classical
  have habZ : (a.val : ℤ) < (b.val : ℤ) := by exact_mod_cast hab
  have hbcZ : (b.val : ℤ) < (c.val : ℤ) := by exact_mod_cast hbc
  have hcn : (c.val : ℤ) < (n : ℤ) := by exact_mod_cast c.isLt
  have ha0 : (0 : ℤ) ≤ a.val := Int.natCast_nonneg _
  have hfullTarget := fullWord_acb_to_bac ρ σ hw
  have hprefix : a ∉ ρ ∧ c ∉ ρ ∧ b ∉ ρ := by
    have hn := hw.1
    simp only [List.nodup_append, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hn
    grind
  obtain ⟨ha, hc, hb⟩ := hprefix
  have hlong_ne : eac ≠ eab := by
    intro heq
    have hl := hacLift.2
    have hs := habLift.2
    rw [heq] at hl
    lia
  have htargetLong : eac ∈ D.strict ∪ η.val := by
    rcases Finset.mem_union.mp hacMem with hs | ha
    · exact Finset.mem_union.mpr (Or.inl hs)
    · apply Finset.mem_union.mpr
      apply Or.inr
      rw [hswap]
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hlong_ne, ha⟩)
  have htargetShort : ebc ∈ D.strict ∪ η.val := by
    apply Finset.mem_union.mpr
    apply Or.inr
    rw [hswap]
    exact Finset.mem_insert_self _ _
  have hsourceAb : D.liftStep θ.val (a.val : ℤ) (b.val : ℤ) :=
    D.liftStep_of_naturalLift_of_mem (Finset.mem_union.mpr (Or.inr habMem)) habLift
  have hsourceAc : D.liftStep θ.val (a.val : ℤ) (c.val : ℤ) :=
    D.liftStep_of_naturalLift_of_mem hacMem hacLift
  have htargetAc : D.liftStep η.val (a.val : ℤ) (c.val : ℤ) :=
    D.liftStep_of_naturalLift_of_mem htargetLong hacLift
  have htargetBc : D.liftStep η.val (b.val : ℤ) (c.val : ℤ) :=
    D.liftStep_of_naturalLift_of_mem htargetShort hbcLift
  have hsourceNot : ¬ D.edgeData.selected θ.val b c := by
    have ht := wordCompatible_middle _ ρ [a, c, b] σ hsource
    simp [wordCompatible, List.pairwise_cons] at ht
    grind
  have htargetNot : ¬ D.edgeData.selected η.val a b := by
    have ht := wordCompatible_middle _ ρ [b, a, c] σ htarget
    simp [wordCompatible, List.pairwise_cons] at ht
    grind
  refine {
    a := (a.val : ℤ)
    b := (b.val : ℤ)
    c := (c.val : ℤ)
    cyclicWindow := ⟨habZ, hbcZ, by lia⟩
    eab := eab
    ebc := ebc
    eab_normal := heab
    ebc_normal := hebc
    ab_lift := habLift
    bc_lift := hbcLift
    source_ab := liftCover_acb_ab ρ σ hw hsource ha hc hb hab hbc hsourceAb
    source_ac := liftCover_acb_ac ρ σ hw hsource ha hc hb hab hbc hsourceAc
    source_not_bc := ?_
    target_ac := liftCover_bac_ac ρ σ hfullTarget htarget ha hc hb hab hbc htargetAc
    target_bc := liftCover_bac_bc ρ σ hfullTarget htarget ha hc hb hab hbc htargetBc
    target_not_ab := ?_
    agree_elsewhere := ?_ }
  · intro hcover
    apply hsourceNot
    have hs := D.liftStep_selected (D.liftCover_liftStep hcover)
    simpa only [Circular.Orientation.residue_intCast_eq] using hs
  · intro hcover
    apply htargetNot
    have hs := D.liftStep_selected (D.liftCover_liftStep hcover)
    simpa only [Circular.Orientation.residue_intCast_eq] using hs
  · intro e hneab hnebc
    rw [hswap]
    simp [hneab, hnebc]

/-- A concrete witness gives the undirected flip used in the component relation. -/
theorem flip_of_directedFlipWitness {θ η : Circular.Orientation D}
    (w : DirectedFlipWitness D θ η) : Flip D θ η :=
  Or.inl ⟨w⟩

/-- An actual directed flip stays in the original complete component. -/
theorem mem_flipComponent_of_directedFlipWitness
    {base θ η : Circular.Orientation D} (hθ : θ ∈ flipComponent D base)
    (w : DirectedFlipWitness D θ η) : η ∈ flipComponent D base := by
  apply mem_flipComponent_iff.mpr
  exact (mem_flipComponent_iff.mp hθ).tail (flip_of_directedFlipWitness w)

end VerticalStripLLT.Components
