import VerticalStripLLT.Circular.InteriorDNRestart
import VerticalStripLLT.Circular.DDLocalRealization

/-! The strict path obtained when the terminal upper row meets an interior
main contact.  This is graph data only; no recurrence is used here. -/

namespace VerticalStripLLT.Circular.Diagram

open scoped Classical

/-- A finite strict path formed by splicing the main contact path into its
parallel translate at an interior alias. -/
structure InteriorMergedComponent {n : ℕ} (D : Diagram n) (t : ℤ)
    (r j : ℕ) where
  two_le : 2 ≤ j
  jump_lt : j < r
  root_eligible : D.EligibleDE t
  vertex : ℕ → Fin n
  main_vertex : ∀ a, a ≤ r →
    vertex a = D.residue (D.boundary^[r - a] t)
  parallel_vertex : ∀ a, a < r →
    vertex (a + j) = D.residue (D.boundary^[r - a] t + 1)
  step : ∀ a, a + 1 < r + j →
    D.edgeData.selected ∅ (vertex a) (vertex (a + 1))
  injective : ∀ ⦃a b⦄, a < r + j → b < r + j → vertex a = vertex b → a = b
  next_jump : ∀ a, a < r → D.area.next (vertex a) = vertex (a + j)
  source : vertex 0 = D.residue (D.boundary^[r] t)
  source_gap : D.eastGap (D.boundary^[r] t) = 0
  root : vertex r = D.residue t
  sink : vertex (r + j - 1) = D.residue (D.boundary t + 1)
  source_free : ∀ v, ¬ D.edgeData.selected ∅ v (vertex 0)
  sink_free : ∀ v, ¬ D.edgeData.selected ∅ (vertex (r + j - 1)) v

namespace DDLocalData

private theorem interior_overlap_propagates
    {n : ℕ} {D : Diagram n} {t x : ℤ} {k i : ℕ}
    (ht : D.EligibleDE t) (h : ReverseBounceN D t x (k + 1))
    (_hi1 : 1 ≤ i) (hik : i ≤ k + 1)
    (hires : D.residue (D.boundary^[i] t) = D.residue (x + 1)) :
    ∀ l, l ≤ i →
      D.residue (D.boundary^[i - l] t) =
        D.residue (D.boundary^[k + 2 - l] t + 1) := by
  obtain ⟨hx, hdd, _, _⟩ := (D.reverseBounceN_iff_iterate).mp h
  subst x
  intro l
  induction l with
  | zero =>
    intro _
    simpa using hires
  | succ l ih =>
    intro hl
    have hmain := bounce_main_step ht.1 hdd (i - (l + 1)) (by lia)
    have hparallel := bounce_parallel_step hdd (k + 1 - l) (by lia) (by lia)
    rw [show i - (l + 1) + 1 = i - l by lia, ih (by lia)] at hmain
    rw [show k + 1 - l + 1 = k + 2 - l by lia] at hparallel
    rw [show k + 2 - (l + 1) = k + 1 - l by lia]
    exact D.strict_selected_rightUnique hmain hparallel

/-- An interior alias cannot be the last DD contact: the local DD datum has
different strict heads at the root and at the translated contact. -/
theorem interior_overlap_le_k
    {n : ℕ} {D : Diagram n} {t x : ℤ} {k i : ℕ}
    (B : D.DDLocalData t) (ht : D.EligibleDE t)
    (h : ReverseBounceN D t x (k + 1))
    (hi1 : 1 ≤ i) (hik : i ≤ k + 1)
    (hires : D.residue (D.boundary^[i] t) = D.residue (x + 1)) : i ≤ k := by
  have hprop := interior_overlap_propagates ht h hi1 hik hires
  have hheads : D.residue (D.boundary t + 1) ≠ D.residue t := by
    rw [← B.gh, ← B.fh]
    intro hgf
    exact B.hfg (D.strict_edge_eq_of_head_eq B.hf B.hg hgf.symm)
  have hroot := hprop i le_rfl
  rw [Nat.sub_self, Function.iterate_zero_apply] at hroot
  by_contra hnot
  have hi : i = k + 1 := by lia
  rw [hi, show k + 2 - (k + 1) = 1 by lia, Function.iterate_one] at hroot
  exact hheads hroot.symm

/-- The original interior DD overlap gives one uniformly indexed, simple
strict path.  The vertices after index `j` are the translated contact path. -/
theorem exists_interiorMergedComponent
    {n : ℕ} {D : Diagram n} {t x : ℤ} {k i : ℕ}
    (B : D.DDLocalData t) (hA : D.edgeData.Admissible ∅) (ht : D.EligibleDE t)
    (h : ReverseBounceN D t x (k + 1))
    (hx : ¬ D.strictAt x) (hx1 : D.strictAt (x + 1))
    (hi1 : 1 ≤ i) (hik : i ≤ k + 1)
    (hires : D.residue (D.boundary^[i] t) = D.residue (x + 1)) :
    Nonempty (InteriorMergedComponent D t (k + 2) (k + 2 - i)) := by
  classical
  have hik' := interior_overlap_le_k B ht h hi1 hik hires
  obtain ⟨hx', hdd, _, _⟩ := (D.reverseBounceN_iff_iterate).mp h
  subst x
  let r : ℕ := k + 2
  let j : ℕ := k + 2 - i
  have hj2 : 2 ≤ j := by
    dsimp [j]
    lia
  have hjpos : 0 < j := by lia
  have hji : j + i = r := by
    dsimp [j, r]
    lia
  have hprop := interior_overlap_propagates ht h hi1 hik hires
  let w : ℕ → Fin n := fun a =>
    if a < j then D.residue (D.boundary^[r - a] t)
    else D.residue (D.boundary^[r - (a - j)] t + 1)
  have w_main (a : ℕ) (ha : a ≤ r) :
      w a = D.residue (D.boundary^[r - a] t) := by
    by_cases haj : a < j
    · simp [w, haj]
    · have hja : j ≤ a := Nat.le_of_not_gt haj
      have hli : a - j ≤ i := by lia
      have hp := hprop (a - j) hli
      simp only [w, ite_eq_right haj]
      rw [show i - (a - j) = r - a by lia] at hp
      exact hp.symm
  have w_parallel (a : ℕ) (ha : a < r) :
      w (a + j) = D.residue (D.boundary^[r - a] t + 1) := by
    have hnot : ¬ a + j < j := by lia
    simp only [w, ite_eq_right hnot]
    congr 3
    lia
  have w_step (a : ℕ) (ha : a + 1 < r + j) :
      D.edgeData.selected ∅ (w a) (w (a + 1)) := by
    by_cases hmain : a + 1 ≤ r
    · rw [w_main a (by lia), w_main (a + 1) hmain]
      have hs := bounce_main_step ht.1 hdd (r - (a + 1)) (by dsimp only [r]; lia)
      rw [show r - (a + 1) + 1 = r - a by lia] at hs
      exact hs
    · have hja : j ≤ a := by lia
      have wa := w_parallel (a - j) (by lia)
      have wa1 := w_parallel (a + 1 - j) (by lia)
      rw [Nat.sub_add_cancel hja] at wa
      rw [Nat.sub_add_cancel (show j ≤ a + 1 by lia)] at wa1
      rw [wa, wa1]
      let q := r - (a + 1 - j)
      have hq1 : 1 ≤ q := by dsimp only [q]; lia
      have hq : q ≤ k + 1 := by dsimp only [q, r]; lia
      have hs := bounce_parallel_step hdd q hq1 hq
      rw [show q + 1 = r - (a - j) by dsimp only [q]; lia] at hs
      exact hs
  have w_injective : ∀ ⦃a b⦄, a < r + j → b < r + j → w a = w b → a = b := by
    intro a b ha hb hab
    have hinj := acyclic_walk_injective (D.edgeData.selected ∅) hA
      (fun z : Fin ((r + j - 1) + 1) => w z.val) (by
        intro z
        exact w_step z (by have := z.isLt; lia))
    exact congrArg Fin.val (@hinj ⟨a, by lia⟩ ⟨b, by lia⟩ hab)
  have w_jump (a : ℕ) (ha : a < r) : D.area.next (w a) = w (a + j) := by
    rw [w_main a (by lia), w_parallel a ha, D.residue_succ]
  have w_source : w 0 = D.residue (D.boundary^[r] t) := w_main 0 (Nat.zero_le _)
  have w_source_gap : D.eastGap (D.boundary^[r] t) = 0 := by
    rw [show D.boundary^[r] t = D.boundary^[k + 2] t by dsimp [r]]
    exact ((D.reverseBounceN_iff_iterate).mp h).2.2.1
  have w_root : w r = D.residue t := by
    rw [w_main r le_rfl, Nat.sub_self, Function.iterate_zero_apply]
  have w_sink : w (r + j - 1) = D.residue (D.boundary t + 1) := by
    have hindex : r + j - 1 = (r - 1) + j := by lia
    rw [hindex, w_parallel (r - 1) (by lia)]
    rw [show r - (r - 1) = 1 by lia, Function.iterate_one]
  refine ⟨⟨hj2, by lia, ht, w, w_main, w_parallel, w_step, w_injective, w_jump, w_source,
    w_source_gap, w_root, w_sink, ?_, ?_⟩⟩
  · intro v
    rw [w_source]
    rw [show D.boundary^[r] t = D.boundary^[k + 2] t by dsimp [r]]
    exact D.not_selected_to_of_not_strictAt hx v
  · intro v
    rw [w_sink]
    exact ht.parallel_end_free D v

end DDLocalData

/-- The public form of the merged-path construction.  The local DD datum is
obtained from the eligible counted bounce. -/
theorem exists_interiorMergedComponent_of_overlap
    {n : ℕ} {D : Diagram n} {t x : ℤ} {k i : ℕ}
    (hA : D.edgeData.Admissible ∅) (ht : D.EligibleDE t)
    (h : ReverseBounceN D t x (k + 1))
    (hx : ¬ D.strictAt x) (hx1 : D.strictAt (x + 1))
    (hi1 : 1 ≤ i) (hik : i ≤ k + 1)
    (hires : D.residue (D.boundary^[i] t) = D.residue (x + 1)) :
    Nonempty (InteriorMergedComponent D t (k + 2) (k + 2 - i)) := by
  obtain ⟨B⟩ := D.exists_ddLocalData ht h
  exact B.exists_interiorMergedComponent hA ht h hx hx1 hi1 hik hires

end VerticalStripLLT.Circular.Diagram
