import VerticalStripLLT.CyclicHessenberg.ColorRuns
import VerticalStripLLT.CyclicHessenberg.CompositionSplit

set_option autoImplicit false

/-! The structural run decomposition used for the sorted-loop order bridge. -/

namespace List

variable {C A : Type*} [LinearOrder C] [LinearOrder A]

/-- Colors increase lexicographically, with labels decreasing within a color. -/
def RunLexOrder (x y : C × A) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ y.2 < x.2)

/-- A constant color block contributes exactly the decreasing-label order. -/
theorem pairwise_zip_replicate_iff (c : C) (l : List A) :
    ((List.replicate l.length c).zip l).Pairwise RunLexOrder ↔
      l.Pairwise (· > ·) := by
  have hzip : (List.replicate l.length c).zip l = l.map fun a => (c, a) := by
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.replicate_succ, ih]
  rw [hzip, List.pairwise_map]
  simp [RunLexOrder]

/-- If composition block sizes are the equality-run lengths, splitting recovers the runs. -/
theorem splitWrtComposition_eq_equalityRuns (colors : List C)
    (β : Composition colors.length)
    (hblocks : β.blocks = (equalityRuns colors).map List.length) :
    colors.splitWrtComposition β = equalityRuns colors := by
  apply List.splitWrtComposition_eq_of_flatten_eq β rfl
    (equalityRuns colors)
  · exact List.flatten_splitBy _ _
  · exact hblocks.symm

/-- The paired blocks are the zips of the color runs and label blocks. -/
theorem splitWrtComposition_zip_eq_runs (colors : List C) (labels : List A)
    (β : Composition colors.length)
    (hblocks : β.blocks = (equalityRuns colors).map List.length) :
    (colors.zip labels).splitWrtComposition β =
      (equalityRuns colors).zipWith List.zip (labels.splitWrtComposition β) := by
  rw [List.splitWrtComposition_zip, splitWrtComposition_eq_equalityRuns _ β hblocks]

private theorem mem_flatten_zipWith_left (R : List (List C)) (B : List (List A))
    (x : C × A) (hx : x ∈ (R.zipWith List.zip B).flatten) : x.1 ∈ R.flatten := by
  induction R generalizing B with
  | nil => simp at hx
  | cons u R ih =>
    cases B with
    | nil => simp at hx
    | cons v B =>
      simp only [List.zipWith_cons_cons, List.flatten_cons, List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (List.of_mem_zip hx).1
      · exact Or.inr (ih B hx)

private theorem pairwise_flatten_zipWith_iff
    (R : List (List C)) (B : List (List A))
    (hlen : R.map List.length = B.map List.length)
    (hconst : ∀ u ∈ R, ∃ c, u = List.replicate u.length c)
    (hcross : R.Pairwise (fun u v => ∀ x ∈ u, ∀ y ∈ v, x < y)) :
    (R.zipWith List.zip B).flatten.Pairwise RunLexOrder ↔
      ∀ b ∈ B, b.Pairwise (· > ·) := by
  induction R generalizing B with
  | nil =>
    have hB : B = [] := List.map_eq_nil_iff.mp hlen.symm
    subst B
    simp
  | cons u R ih =>
    cases B with
    | nil => simp at hlen
    | cons v B =>
      have hlengths := List.cons.inj hlen
      have hpair := List.pairwise_cons.mp hcross
      obtain ⟨c, hc⟩ := hconst u (by simp)
      have hhead : (u.zip v).Pairwise RunLexOrder ↔ v.Pairwise (· > ·) := by
        rw [hc, hlengths.1]
        exact pairwise_zip_replicate_iff c v
      have htail := ih B hlengths.2
        (fun w hw => hconst w (List.mem_cons_of_mem _ hw)) hpair.2
      have hbetween : ∀ x ∈ u.zip v, ∀ y ∈ (R.zipWith List.zip B).flatten,
          RunLexOrder x y := by
        intro x hx y hy
        obtain ⟨w, hw, hyw⟩ := List.mem_flatten.mp (mem_flatten_zipWith_left R B y hy)
        exact Or.inl (hpair.1 w hw x.1 (List.of_mem_zip hx).1 y.1 hyw)
      simp only [List.zipWith_cons_cons, List.flatten_cons, List.pairwise_append]
      rw [hhead, htail]
      simp only [List.mem_cons, forall_eq_or_imp]
      tauto

theorem equalityRuns_pairwise_cross {colors : List C} (hc : colors.Pairwise (· ≤ ·)) :
    colors.equalityRuns.Pairwise (fun u v => ∀ x ∈ u, ∀ y ∈ v, x < y) := by
  have hh := equalityRunHeads_pairwise_lt hc
  unfold equalityRunHeads at hh
  rw [List.pairwise_pmap] at hh
  apply hh.imp_of_mem
  intro u v hu hv huv x hx y hy
  have hux : x = u.head (mem_equalityRun_ne_nil hu) := by
    have hm : x ∈ List.replicate u.length (u.head (mem_equalityRun_ne_nil hu)) :=
      equalityRun_eq_replicate_head hu ▸ hx
    exact (List.mem_replicate.mp hm).2
  have hvy : y = v.head (mem_equalityRun_ne_nil hv) := by
    have hm : y ∈ List.replicate v.length (v.head (mem_equalityRun_ne_nil hv)) :=
      equalityRun_eq_replicate_head hv ▸ hy
    exact (List.mem_replicate.mp hm).2
  rw [hux, hvy]
  exact huv _ _

/-- Lexicographic color/tie order is precisely decreasing order within the positive runs. -/
theorem pairwise_zip_eqRuns_iff_blocks_desc (colors : List C) (labels : List A)
    (β : Composition colors.length) (hcolors : colors.Pairwise (· ≤ ·))
    (hlen : labels.length = colors.length)
    (hblocks : β.blocks = (equalityRuns colors).map List.length) :
    (colors.zip labels).Pairwise RunLexOrder ↔
      ∀ block ∈ labels.splitWrtComposition β, block.Pairwise (· > ·) := by
  have hflat : ((colors.zip labels).splitWrtComposition β).flatten = colors.zip labels := by
    apply List.flatten_splitWrtCompositionAux
    rw [β.blocks_sum, List.length_zip, hlen, Nat.min_self]
  rw [← hflat, splitWrtComposition_zip_eq_runs colors labels β hblocks]
  apply pairwise_flatten_zipWith_iff
  · rw [← hblocks]
    symm
    apply List.map_length_splitWrtCompositionAux
    rw [β.blocks_sum, hlen]
  · intro u hu
    exact ⟨u.head (mem_equalityRun_ne_nil hu), equalityRun_eq_replicate_head hu⟩
  · exact equalityRuns_pairwise_cross hcolors

theorem pairwise_zip_composition_iff_blocks_desc {k : ℕ}
    (colors : List C) (labels : List A) (β : Composition k)
    (hclen : colors.length = k) (hllen : labels.length = k)
    (hcolors : colors.Pairwise (· ≤ ·))
    (hblocks : β.blocks = (equalityRuns colors).map List.length) :
    (colors.zip labels).Pairwise RunLexOrder ↔
      ∀ block ∈ labels.splitWrtComposition β, block.Pairwise (· > ·) := by
  subst k
  exact pairwise_zip_eqRuns_iff_blocks_desc colors labels β hcolors hllen hblocks

end List
