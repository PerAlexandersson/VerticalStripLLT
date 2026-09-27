import VerticalStripLLT.Components.ComponentWords
import VerticalStripLLT.Components.LiftCoverRank

/-! Cover certificates obtained from the positions of a full compatible word.

Word positions increase along actual selected edges. The cover lemmas require
only a full compatible word; the component wrappers add filtered membership
when that is already available.
-/

namespace VerticalStripLLT.Components

open Circular

variable {n : ℕ} {D : Diagram n}

private theorem word_rank_increases_on_selected
    {η : Circular.Orientation D} {w : List (Fin n)} (hw : fullWord w)
    (hcompat : wordCompatible (D.edgeData.selected η.val) w) :
    ∀ ⦃u v : Fin n⦄, D.edgeData.selected η.val u v →
      w.idxOf u < w.idxOf v := by
  intro u v huv
  apply wordCompatible_idxOf_lt (D.edgeData.selected η.val) w
    (fun x hx => η.property.2 x (Relation.TransGen.single hx))
    hcompat (hw.2 u) (hw.2 v) huv

/-- A selected lifted step whose word ranks are consecutive is a full integer
cover, assuming only compatibility of the selected relation with the word. -/
theorem liftCover_of_wordCompatible_rank_succ
    {η : Circular.Orientation D} {w : List (Fin n)} (hw : fullWord w)
    (hcompat : wordCompatible (D.edgeData.selected η.val) w)
    {x y : ℤ} (hstep : D.liftStep η.val x y)
    (hsucc : w.idxOf (D.residue y) = w.idxOf (D.residue x) + 1) :
    D.liftCover η.val x y := by
  apply Circular.Diagram.liftCover_of_liftStep_rank_succ
    (fun v : Fin n => w.idxOf v)
    (word_rank_increases_on_selected hw hcompat) hstep
  exact hsucc

/-- A selected lifted step whose word ranks are consecutive is a full integer
cover. -/
theorem liftCover_of_full_compatible_word_rank_succ
    (θ : Circular.Orientation D) {η : Circular.Orientation D}
    {w : List (Fin n)} (hw : fullWord w)
    (hη : η ∈ compatibleComponent D θ w)
    {x y : ℤ} (hstep : D.liftStep η.val x y)
    (hsucc : w.idxOf (D.residue y) = w.idxOf (D.residue x) + 1) :
    D.liftCover η.val x y := by
  apply Circular.Diagram.liftCover_of_liftStep_rank_succ
    (fun v : Fin n => w.idxOf v) (word_rank_increases_on_selected hw
      ((mem_compatibleComponent θ η w).mp hη).2) hstep
  exact hsucc

/-- A rank-gap cover certificate assuming only compatibility of the selected
relation with the word. -/
theorem liftCover_of_wordCompatible_rank_gap
    {η : Circular.Orientation D} {w : List (Fin n)} (hw : fullWord w)
    (hcompat : wordCompatible (D.edgeData.selected η.val) w)
    {x y : ℤ} (hstep : D.liftStep η.val x y)
    (hgap : ∀ z, x < z → z < y →
      ¬ (w.idxOf (D.residue x) < w.idxOf (D.residue z) ∧
        w.idxOf (D.residue z) < w.idxOf (D.residue y))) :
    D.liftCover η.val x y := by
  apply Circular.Diagram.liftCover_of_liftStep_rank_gap
    (fun v : Fin n => w.idxOf v)
    (word_rank_increases_on_selected hw hcompat) hstep
  exact hgap

/-- A full compatible word supplies the rank-gap version of the lifted-cover
certificate. -/
theorem liftCover_of_full_compatible_word_rank_gap
    (θ : Circular.Orientation D) {η : Circular.Orientation D}
    {w : List (Fin n)} (hw : fullWord w)
    (hη : η ∈ compatibleComponent D θ w)
    {x y : ℤ} (hstep : D.liftStep η.val x y)
    (hgap : ∀ z, x < z → z < y →
      ¬ (w.idxOf (D.residue x) < w.idxOf (D.residue z) ∧
        w.idxOf (D.residue z) < w.idxOf (D.residue y))) :
    D.liftCover η.val x y := by
  exact liftCover_of_wordCompatible_rank_gap hw
    ((mem_compatibleComponent θ η w).mp hη).2 hstep hgap

/-- A rank-two cover certificate assuming only compatibility of the selected
relation with the word. -/
theorem liftCover_of_wordCompatible_rank_two
    {η : Circular.Orientation D} {w : List (Fin n)} (hw : fullWord w)
    (hcompat : wordCompatible (D.edgeData.selected η.val) w)
    {x y : ℤ} (hstep : D.liftStep η.val x y)
    (middle : Fin n)
    (hmiddle : ∀ z, x < z → z < y → D.residue z ≠ middle)
    (hleft : w.idxOf middle = w.idxOf (D.residue x) + 1)
    (hright : w.idxOf (D.residue y) = w.idxOf (D.residue x) + 2) :
    D.liftCover η.val x y := by
  apply liftCover_of_wordCompatible_rank_gap hw hcompat hstep
  intro z hxz hzy hfactor
  have hzrank : w.idxOf (D.residue z) = w.idxOf (D.residue x) + 1 := by
    rw [hright] at hfactor
    lia
  have hres : D.residue z = middle := by
    exact (List.idxOf_inj (hw.2 (D.residue z))).mp (hzrank.trans hleft.symm)
  exact hmiddle z hxz hzy hres

/-- If the only possible intermediate rank is the rank of middle, and no
integer in the lifted interval has that residue, then a rank-two step is a
full integer cover. -/
theorem liftCover_of_full_compatible_word_rank_two
    (θ : Circular.Orientation D) {η : Circular.Orientation D}
    {w : List (Fin n)} (hw : fullWord w)
    (hη : η ∈ compatibleComponent D θ w)
    {x y : ℤ} (hstep : D.liftStep η.val x y)
    (middle : Fin n)
    (hmiddle : ∀ z, x < z → z < y → D.residue z ≠ middle)
    (hleft : w.idxOf middle = w.idxOf (D.residue x) + 1)
    (hright : w.idxOf (D.residue y) = w.idxOf (D.residue x) + 2) :
    D.liftCover η.val x y := by
  exact liftCover_of_wordCompatible_rank_two hw
    ((mem_compatibleComponent θ η w).mp hη).2 hstep middle hmiddle hleft hright

/-- The positions of a triple occurring contiguously in a full word.  This is
the small list calculation used by the rank-two cover adapter. -/
theorem idxOf_triple
    (ρ σ : List (Fin n)) {a c b : Fin n}
    (ha : a ∉ ρ) (hc : c ∉ ρ) (hb : b ∉ ρ)
    (hca : c ≠ a) (hba : b ≠ a) (hbc : b ≠ c) :
    (ρ ++ [a, c, b] ++ σ).idxOf a = ρ.length ∧
      (ρ ++ [a, c, b] ++ σ).idxOf c = ρ.length + 1 ∧
      (ρ ++ [a, c, b] ++ σ).idxOf b = ρ.length + 2 := by
  have hc' : c ∉ ρ ++ [a] := by
    simp [hc, hca]
  have hb' : b ∉ ρ ++ [a, c] := by
    simp [hb, hba, hbc]
  have ha' := idxOf_middle ρ ([c, b] ++ σ) ha
  have hc'' := idxOf_middle (ρ ++ [a]) ([b] ++ σ) hc'
  have hb'' := idxOf_middle (ρ ++ [a, c]) σ hb'
  refine ⟨?_, ?_, ?_⟩
  · simpa [List.append_assoc] using ha'
  · simpa [List.append_assoc] using hc''
  · simpa [List.append_assoc] using hb''

/-- A residue strictly between two canonical representatives cannot be a
larger canonical vertex.  This is the no-wrap fact used for the rank-two
cover of the edge from `a` to `b` when `b < c`. -/
theorem residue_ne_of_canonical_between
    (a b c : Fin n) (hbc : b < c) {z : ℤ}
    (haz : (a.val : ℤ) < z) (hzb : z < (b.val : ℤ)) :
    D.residue z ≠ c := by
  intro hzc
  have hz0 : (0 : ℤ) ≤ z := by
    have ha0 : (0 : ℤ) ≤ a.val := by positivity
    lia
  have hzn : z < (n : ℤ) := by
    have hbn : (b.val : ℤ) < (n : ℤ) := by exact_mod_cast b.isLt
    lia
  have hmod : z % (n : ℤ) = z := Int.emod_eq_of_lt hz0 hzn
  have hval := congrArg (fun v : Fin n => (v.val : ℤ)) hzc
  rw [D.residue_coe_val, hmod] at hval
  have hbc' : (b.val : ℤ) < (c.val : ℤ) := by exact_mod_cast hbc
  lia

/-- The symmetric no-wrap fact for the interval from `b` to `c`. -/
theorem residue_ne_of_canonical_between_left
    (a b c : Fin n) (hab : a < b) {z : ℤ}
    (hzb : (b.val : ℤ) < z) (hzc : z < (c.val : ℤ)) :
    D.residue z ≠ a := by
  intro hza
  have hz0 : (0 : ℤ) ≤ z := by
    have hb0 : (0 : ℤ) ≤ b.val := by positivity
    lia
  have hzn : z < (n : ℤ) := by
    have hcn : (c.val : ℤ) < (n : ℤ) := by exact_mod_cast c.isLt
    lia
  have hmod : z % (n : ℤ) = z := Int.emod_eq_of_lt hz0 hzn
  have hval := congrArg (fun v : Fin n => (v.val : ℤ)) hza
  rw [D.residue_coe_val, hmod] at hval
  have hab' : (a.val : ℤ) < (b.val : ℤ) := by exact_mod_cast hab
  lia

/-- The consecutive and rank-two source covers for an `acb` word. -/
theorem liftCover_acb_ac
    {η : Circular.Orientation D} (ρ σ : List (Fin n))
    {a b c : Fin n} (hw : fullWord (ρ ++ [a, c, b] ++ σ))
    (hcompat : wordCompatible (D.edgeData.selected η.val)
      (ρ ++ [a, c, b] ++ σ))
    (ha : a ∉ ρ) (hc : c ∉ ρ) (hb : b ∉ ρ)
    (hab : a < b) (hbc : b < c)
    (hstep : D.liftStep η.val (a.val : ℤ) (c.val : ℤ)) :
    D.liftCover η.val (a.val : ℤ) (c.val : ℤ) := by
  have hi := idxOf_triple ρ σ ha hc hb
    (ne_of_gt (lt_trans hab hbc)) (ne_of_gt hab) (ne_of_lt hbc)
  apply liftCover_of_wordCompatible_rank_succ hw hcompat hstep
  simp only [Circular.Orientation.residue_intCast_eq, hi.2.1, hi.1]

theorem liftCover_acb_ab
    {η : Circular.Orientation D} (ρ σ : List (Fin n))
    {a b c : Fin n} (hw : fullWord (ρ ++ [a, c, b] ++ σ))
    (hcompat : wordCompatible (D.edgeData.selected η.val)
      (ρ ++ [a, c, b] ++ σ))
    (ha : a ∉ ρ) (hc : c ∉ ρ) (hb : b ∉ ρ)
    (hab : a < b) (hbc : b < c)
    (hstep : D.liftStep η.val (a.val : ℤ) (b.val : ℤ)) :
    D.liftCover η.val (a.val : ℤ) (b.val : ℤ) := by
  have hi := idxOf_triple ρ σ ha hc hb
    (ne_of_gt (lt_trans hab hbc)) (ne_of_gt hab) (ne_of_lt hbc)
  apply liftCover_of_wordCompatible_rank_two hw hcompat hstep c
  · intro z haz hzb
    exact residue_ne_of_canonical_between (D := D) a b c hbc haz hzb
  · simp only [Circular.Orientation.residue_intCast_eq, hi.2.1, hi.1]
  · simp only [Circular.Orientation.residue_intCast_eq, hi.2.2, hi.1]

/-- The consecutive and rank-two target covers for a `bac` word. -/
theorem liftCover_bac_ac
    {η : Circular.Orientation D} (ρ σ : List (Fin n))
    {a b c : Fin n} (hw : fullWord (ρ ++ [b, a, c] ++ σ))
    (hcompat : wordCompatible (D.edgeData.selected η.val)
      (ρ ++ [b, a, c] ++ σ))
    (ha : a ∉ ρ) (hc : c ∉ ρ) (hb : b ∉ ρ)
    (hab : a < b) (hbc : b < c)
    (hstep : D.liftStep η.val (a.val : ℤ) (c.val : ℤ)) :
    D.liftCover η.val (a.val : ℤ) (c.val : ℤ) := by
  have hi := idxOf_triple (a := b) (c := a) (b := c) ρ σ hb ha hc
    (ne_of_lt hab) (ne_of_gt hbc) (ne_of_gt (lt_trans hab hbc))
  apply liftCover_of_wordCompatible_rank_succ hw hcompat hstep
  simp only [Circular.Orientation.residue_intCast_eq, hi.2.2, hi.2.1]

theorem liftCover_bac_bc
    {η : Circular.Orientation D} (ρ σ : List (Fin n))
    {a b c : Fin n} (hw : fullWord (ρ ++ [b, a, c] ++ σ))
    (hcompat : wordCompatible (D.edgeData.selected η.val)
      (ρ ++ [b, a, c] ++ σ))
    (ha : a ∉ ρ) (hc : c ∉ ρ) (hb : b ∉ ρ)
    (hab : a < b) (hbc : b < c)
    (hstep : D.liftStep η.val (b.val : ℤ) (c.val : ℤ)) :
    D.liftCover η.val (b.val : ℤ) (c.val : ℤ) := by
  have hi := idxOf_triple (a := b) (c := a) (b := c) ρ σ hb ha hc
    (ne_of_lt hab) (ne_of_gt hbc) (ne_of_gt (lt_trans hab hbc))
  apply liftCover_of_wordCompatible_rank_two hw hcompat hstep a
  · intro z hzb hzc
    exact residue_ne_of_canonical_between_left (D := D) a b c hab hzb hzc
  · simp only [Circular.Orientation.residue_intCast_eq, hi.2.1, hi.1]
  · simp only [Circular.Orientation.residue_intCast_eq, hi.2.2, hi.1]

end VerticalStripLLT.Components
