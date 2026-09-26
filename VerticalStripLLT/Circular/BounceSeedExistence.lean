import VerticalStripLLT.Circular.BoundaryRow
import VerticalStripLLT.Circular.CutOrder
import VerticalStripLLT.Circular.StrictCycle
import Mathlib.Tactic.Linarith

/-! An acyclic saturated diagram with a normal edge has a strict row before an east gap. -/

namespace VerticalStripLLT.Circular

namespace Diagram

variable {n : ℕ} (D : Diagram n)

private theorem exists_area_ge_two
    (hsat : ∀ e, IsCorner e → e ∈ D.strict)
    (hn : D.edgeData.normalEdges.Nonempty) :
    ∃ v, 2 ≤ D.area.area v := by
  classical
  obtain ⟨e, he⟩ := hn
  have henot : e ∉ D.strict := by
    rw [EdgeData.normalEdges] at he
    exact (Finset.mem_sdiff.mp he).2
  by_contra h
  push Not at h
  have hhead : D.area.area e.head ≤ 1 := by have := h e.head; lia
  have hnext : D.area.area (D.area.next e.head) ≤ 1 := by
    have := h (D.area.next e.head)
    lia
  have hlen : e.length.val = 1 := by
    have hp := e.length_pos
    have hle := e.length_le_area
    lia
  have harea : D.area.area e.head = 1 := by
    have hle := e.length_le_area
    rw [hlen] at hle
    lia
  have hcorner : IsCorner e := by
    refine ⟨?_, ?_⟩
    · rw [hlen, harea]
    · rw [harea]
      exact hnext
  exact henot (hsat e hcorner)

private theorem residue_intCast (v : Fin n) : D.residue (v.val : ℤ) = v := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [D.residue_coe_val]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast v.isLt)

/-- A maximal positive row must exit its plateau unless strict edges already form a cycle. -/
theorem exists_eligible_seed
    (hsat : ∀ e, IsCorner e → e ∈ D.strict)
    (ha : D.edgeData.Admissible ∅) (hn : D.edgeData.normalEdges.Nonempty) :
    ∃ z : ℤ, D.strictAt z ∧ 2 ≤ D.area.area (D.residue z) ∧ 0 < D.eastGap z := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, D.area.positive⟩⟩
  obtain ⟨w, hw⟩ := D.exists_area_ge_two hsat hn
  obtain ⟨v, _, hvmax⟩ :=
    Finset.exists_max_image Finset.univ D.area.area Finset.univ_nonempty
  have hvlarge : 2 ≤ D.area.area v := hw.trans (hvmax w (Finset.mem_univ _))
  have hexit : ∃ u, D.area.area u = D.area.area v ∧
      D.area.area (D.area.next u) < D.area.area v := by
    by_contra hnone
    have hno : ∀ u, D.area.area u = D.area.area v →
        ¬ D.area.area (D.area.next u) < D.area.area v := by
      intro u hu hlt
      exact hnone ⟨u, hu, hlt⟩
    have hoffset : ∀ k : ℕ, D.area.area (D.area.atOffset v k) = D.area.area v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [D.area.atOffset_succ]
        apply Nat.le_antisymm
        · exact hvmax _ (Finset.mem_univ _)
        · by_contra hlt
          have hlt' : D.area.area (D.area.next (D.area.atOffset v k)) < D.area.area v :=
            Nat.lt_of_not_ge hlt
          exact hno _ ih hlt'
    have hsurj : Function.Surjective (fun k : Fin n => D.area.atOffset v k.val) :=
      Finite.surjective_of_injective (D.area.atOffset_fin_injective v)
    have hall : ∀ u, D.area.area u = D.area.area v := by
      intro u
      obtain ⟨k, hk⟩ := hsurj u
      rw [← hk]
      exact hoffset k.val
    have hin : ∀ u, ∃ e ∈ D.strict, e.head = u := by
      intro u
      let e : Edge D.area :=
        ⟨(u, ⟨D.area.area v, by rw [← hall u]; exact D.area.bound u⟩),
          ⟨by have := hvlarge; lia, by exact (hall u).symm.le⟩⟩
      have hcorner : IsCorner e := by
        refine ⟨?_, ?_⟩
        · change D.area.area v = D.area.area u
          exact (hall u).symm
        · change D.area.area (D.area.next u) ≤ D.area.area u
          rw [hall (D.area.next u), hall u]
      exact ⟨e, hsat e hcorner, rfl⟩
    exact (D.edgeData.not_Admissible_of_strict_incoming hin ∅) ha
  obtain ⟨u, hu, hdrop⟩ := hexit
  have hularge : 2 ≤ D.area.area u := by rw [hu]; exact hvlarge
  have hdropu : D.area.area (D.area.next u) < D.area.area u := by
    rwa [hu]
  refine ⟨(u.val : ℤ), ?_, ?_, ?_⟩
  · have hres := D.residue_intCast u
    have hres' : D.residue ((u.val : ℤ) + 1) = D.area.next u := by
      rw [D.residue_succ, hres]
    have hstep : D.boundary (u.val : ℤ) < D.boundary ((u.val : ℤ) + 1) := by
      rw [Diagram.boundary, Diagram.boundary, hres, hres']
      have hdrop' : (D.area.area (D.area.next u) : ℤ) < D.area.area u := by
        exact_mod_cast hdropu
      linarith
    exact D.strictAt_of_boundary_step hsat (by rw [hres]; lia) hstep
  · rw [D.residue_intCast]
    exact hularge
  · have hres := D.residue_intCast u
    have hres' : D.residue ((u.val : ℤ) + 1) = D.area.next u := by
      rw [D.residue_succ, hres]
    have hs : D.strictAt (u.val : ℤ) := by
      have hstep : D.boundary (u.val : ℤ) < D.boundary ((u.val : ℤ) + 1) := by
        rw [Diagram.boundary, Diagram.boundary, hres, hres']
        have hdrop' : (D.area.area (D.area.next u) : ℤ) < D.area.area u := by
          exact_mod_cast hdropu
        linarith
      exact D.strictAt_of_boundary_step hsat (by rw [hres]; lia) hstep
    unfold eastGap
    rw [ite_eq_left hs, Diagram.boundary, Diagram.boundary, hres, hres']
    have hdrop' : (D.area.area (D.area.next u) : ℤ) < D.area.area u := by
      exact_mod_cast hdropu
    linarith

end Diagram

end VerticalStripLLT.Circular
