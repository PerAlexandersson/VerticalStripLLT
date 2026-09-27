import VerticalStripLLT.Components.ComponentWords
import VerticalStripLLT.Components.LiftCoverRank

/-! Cover certificates obtained from the positions of a full compatible word.

The rank used here is the position in the word.  The hypotheses on a word are
kept explicit: the cover lemmas apply to an actual member of the filtered
component, and hence do not identify a recurrence-defined relation with the
coloring relation.
-/

namespace VerticalStripLLT.Components

open Circular

variable {n : ℕ} {D : Diagram n}

private theorem word_rank_increases_on_selected
    (θ : Circular.Orientation D) {η : Circular.Orientation D}
    {w : List (Fin n)} (hw : fullWord w)
    (hη : η ∈ compatibleComponent D θ w) :
    ∀ ⦃u v : Fin n⦄, D.edgeData.selected η.val u v →
      w.idxOf u < w.idxOf v := by
  intro u v huv
  exact compatibleComponent_idxOf_lt θ hw hη huv

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
    (fun v : Fin n => w.idxOf v)
    (word_rank_increases_on_selected θ hw hη) hstep
  exact hsucc

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
  apply Circular.Diagram.liftCover_of_liftStep_rank_gap
    (fun v : Fin n => w.idxOf v)
    (word_rank_increases_on_selected θ hw hη) hstep
  exact hgap

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
  apply liftCover_of_full_compatible_word_rank_gap θ hw hη hstep
  intro z hxz hzy hfactor
  have hzrank : w.idxOf (D.residue z) = w.idxOf (D.residue x) + 1 := by
    rw [hright] at hfactor
    lia
  have hres : D.residue z = middle := by
    exact (List.idxOf_inj (hw.2 (D.residue z))).mp (hzrank.trans hleft.symm)
  exact hmiddle z hxz hzy hres

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

end VerticalStripLLT.Components
