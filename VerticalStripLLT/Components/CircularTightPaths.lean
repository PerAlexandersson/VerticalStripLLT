import VerticalStripLLT.Components.TightReachability
import VerticalStripLLT.Circular.HRVPotential
import VerticalStripLLT.Circular.LiftCover

/-! Tight selected paths and covers in the full integer lift. -/

namespace VerticalStripLLT.Circular.Diagram

variable {n : ℕ} (D : Diagram n)

/-- Subtracting integer displacement makes each tight lifted edge score-preserving. -/
def liftScore (M : ℤ) (z : Fin n → ℤ) (t : ℤ) : ℤ := z (D.residue t) - M * t

theorem liftScore_eq_of_naturalLift {M : ℤ} {z : Fin n → ℤ}
    {e : Edge D.area} {a b : ℤ} (h : D.naturalLift e a b)
    (heq : z e.head - z e.tail = M * (e.length.val : ℤ)) :
    D.liftScore M z a = D.liftScore M z b := by
  obtain ⟨ha, rfl⟩ := h
  have hb := D.residue_add_length e a ha
  simp only [liftScore, ha, hb, mul_add]
  lia

theorem admissible_of_scaled_potential {X : Finset (Edge D.area)} {M : ℤ}
    {z : Fin n → ℤ} (hM : 0 < M)
    (hweak : ∀ e ∈ D.strict ∪ X, M * (e.length.val : ℤ) ≤ z e.head - z e.tail) :
    D.edgeData.Admissible X := by
  have hinc {u v : Fin n} (h : D.edgeData.selected X u v) : z u < z v := by
    obtain ⟨e, he, rfl, rfl⟩ := h
    change z e.tail < z e.head
    have hpos : (0 : ℤ) < e.length.val := by exact_mod_cast e.length_pos
    have hp := mul_pos hM hpos
    have hw := hweak e he
    lia
  have hpath {u v : Fin n} (h : Relation.TransGen (D.edgeData.selected X) u v) :
      z u < z v := by
    induction h with
    | single hs => exact hinc hs
    | tail _ hs ih => exact ih.trans (hinc hs)
  intro v hcycle
  exact lt_irrefl _ (hpath hcycle)

theorem liftScore_le_of_step {X : Finset (Edge D.area)} {M : ℤ} {z : Fin n → ℤ}
    (hweak : ∀ e ∈ D.strict ∪ X, M * (e.length.val : ℤ) ≤ z e.head - z e.tail)
    {a b : ℤ} (h : D.liftStep X a b) : D.liftScore M z a ≤ D.liftScore M z b := by
  obtain ⟨e, he, ha, rfl⟩ := h
  have hb := D.residue_add_length e a ha
  have hle := hweak e he
  simp only [liftScore, ha, hb, mul_add]
  lia

theorem liftStep_of_tight_score {X F : Finset (Edge D.area)} {M : ℤ}
    {z : Fin n → ℤ}
    (htight : ∀ e ∈ D.strict ∪ X,
      z e.head - z e.tail = M * (e.length.val : ℤ) → e ∈ D.strict ∪ F)
    {a b : ℤ} (h : D.liftStep X a b) (heq : D.liftScore M z a = D.liftScore M z b) :
    D.liftStep F a b := by
  obtain ⟨e, he, ha, rfl⟩ := h
  have hb := D.residue_add_length e a ha
  refine ⟨e, htight e he ?_, ha, rfl⟩
  simp only [liftScore, ha, hb, mul_add] at heq
  lia

/-- Every competing lifted path between tight endpoints stays in the tight selection. -/
theorem liftReach_of_tight_score {X F : Finset (Edge D.area)} {M : ℤ}
    {z : Fin n → ℤ}
    (hweak : ∀ e ∈ D.strict ∪ X, M * (e.length.val : ℤ) ≤ z e.head - z e.tail)
    (htight : ∀ e ∈ D.strict ∪ X,
      z e.head - z e.tail = M * (e.length.val : ℤ) → e ∈ D.strict ∪ F)
    {a b : ℤ} (h : Relation.ReflTransGen (D.liftStep X) a b)
    (heq : D.liftScore M z a = D.liftScore M z b) :
    Relation.ReflTransGen (D.liftStep F) a b :=
  Components.reachable_of_tight_score _ _ (D.liftScore M z)
    (fun {_ _} hs => D.liftScore_le_of_step hweak hs)
    (fun {_ _} hs he => D.liftStep_of_tight_score htight hs he) h heq

/-- A tight cover stays a cover after adjoining only strictly slack edges. -/
theorem liftCover_of_tight_score {X F : Finset (Edge D.area)} {M : ℤ}
    {z : Fin n → ℤ} (hFX : F ⊆ X)
    (hweak : ∀ e ∈ D.strict ∪ X, M * (e.length.val : ℤ) ≤ z e.head - z e.tail)
    (htight : ∀ e ∈ D.strict ∪ X,
      z e.head - z e.tail = M * (e.length.val : ℤ) → e ∈ D.strict ∪ F)
    {a b : ℤ} (hcover : D.liftCover F a b)
    (heq : D.liftScore M z a = D.liftScore M z b) : D.liftCover X a b := by
  have hmono : ∀ ⦃u v⦄, D.liftStep X u v → D.liftScore M z u ≤ D.liftScore M z v :=
    fun {_ _} h => D.liftScore_le_of_step hweak h
  refine ⟨hcover.1, ?_, ?_⟩
  · apply Relation.ReflTransGen.mono ?_ _ _ hcover.2.1
    rintro u v ⟨e, he, hnat⟩
    exact ⟨e, (Finset.union_subset_union_right hFX) he, hnat⟩
  · intro c hac hcb hpaths
    have hac' := Components.score_le_of_reachable _ _ hmono hpaths.1
    have hcb' := Components.score_le_of_reachable _ _ hmono hpaths.2
    have heqac : D.liftScore M z a = D.liftScore M z c :=
      le_antisymm hac' (by simpa [heq] using hcb')
    exact hcover.2.2 c hac hcb
      ⟨D.liftReach_of_tight_score hweak htight hpaths.1 heqac,
        D.liftReach_of_tight_score hweak htight hpaths.2 (heqac.symm.trans heq)⟩

theorem liftCover_tight_iff {X F : Finset (Edge D.area)} {M : ℤ}
    {z : Fin n → ℤ} (hFX : F ⊆ X)
    (hweak : ∀ e ∈ D.strict ∪ X, M * (e.length.val : ℤ) ≤ z e.head - z e.tail)
    (htight : ∀ e ∈ D.strict ∪ X,
      z e.head - z e.tail = M * (e.length.val : ℤ) → e ∈ D.strict ∪ F)
    {a b : ℤ} (heq : D.liftScore M z a = D.liftScore M z b) :
    D.liftCover X a b ↔ D.liftCover F a b := by
  refine ⟨?_, fun hc => D.liftCover_of_tight_score hFX hweak htight hc heq⟩
  intro hc
  have hmono {u v : ℤ} (h : Relation.ReflTransGen (D.liftStep F) u v) :
      Relation.ReflTransGen (D.liftStep X) u v := by
    apply Relation.ReflTransGen.mono ?_ _ _ h
    rintro x y ⟨e, he, hnat⟩
    exact ⟨e, (Finset.union_subset_union_right hFX) he, hnat⟩
  refine ⟨hc.1, D.liftReach_of_tight_score hweak htight hc.2.1 heq, ?_⟩
  intro c hac hcb hpaths
  exact hc.2.2 c hac hcb ⟨hmono hpaths.1, hmono hpaths.2⟩

end VerticalStripLLT.Circular.Diagram
