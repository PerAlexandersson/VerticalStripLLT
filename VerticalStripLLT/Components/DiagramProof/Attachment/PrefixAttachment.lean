import VerticalStripLLT.Components.DiagramProof.Attachment.AttachmentWitness

/-!
# The first nontrivial prefix and its right attachment

In a connected ordinary diagram an internal vertex `v` is an articulation exactly
when `a_(v+1) = 1`. Let `j` be the first vertex with `a_j ≥ 2`, put `b = j - 2`,
and let `c ≥ j` be the first vertex with `c` last or `a_(c+1) = 1`. The prefix on
`[0, c]` is an initial path to `b` followed by a block without articulation, and
no natural edge crosses `c`. Its witness component has a right-marked certificate
by the first drop; gluing the fixed attachment on `[c, n-1]` to every term gives an
unmarked certificate of the original component.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k : ℕ} {D : Diagram (k + 1)} (hD : Forward D)

include hD in
/-- Every natural pair between the endpoints of a natural pair is natural. -/
theorem naturalRel_sub {p q a b : Fin (k + 1)} (h : naturalRel D p q) (hpa : p ≤ a)
    (hab : a < b) (hbq : b ≤ q) : naturalRel D a b := by
  have hpb : naturalRel D p b := by
    rcases lt_or_eq_of_le hbq with hbq | rfl
    · exact (naturalRel_interval hD h (hpa.trans_lt hab) hbq).1
    · exact h
  rcases lt_or_eq_of_le hpa with hpa | rfl
  · exact (naturalRel_interval hD hpb hpa hab).2
  · exact hpb

include hD in
/-- **The first nontrivial prefix.** -/
theorem exists_prefix (hadj : AdjacentEdges D)
    (hnp : ∃ u v : Fin (k + 1), naturalRel D u v ∧ u.val + 2 ≤ v.val) :
    ∃ c b : ℕ, c ≤ k ∧ b + 2 ≤ c ∧
      (∀ e : Edge D.area, e.tail.val < c → e.head.val ≤ c) ∧
      (∀ u v : Fin (k + 1), naturalRel D u v → u.val < b → v.val = u.val + 1) ∧
      (∀ u v : Fin (k + 1), b ≤ u.val → u < v → v.val ≤ u.val + 2 → v.val ≤ c →
        naturalRel D u v) ∧
      (∃ u v : Fin (k + 1), naturalRel D u v ∧ u.val + 2 ≤ v.val ∧ v.val ≤ c) := by
  -- Natural pairs of length two.
  let N2 : ℕ → Prop := fun v => ∃ hv : v < k + 1, 2 ≤ v ∧
    naturalRel D ⟨v - 2, by lia⟩ ⟨v, hv⟩
  have hN2 : ∃ v, N2 v := by
    obtain ⟨u, w, huw, hgap⟩ := hnp
    exact ⟨w.val, w.isLt, by lia, naturalRel_sub hD huw (by rw [Fin.le_def]; simp; lia)
      (by rw [Fin.lt_def]; simp; lia) le_rfl⟩
  let j := Nat.find hN2
  have hj : N2 j := Nat.find_spec hN2
  have hjmin : ∀ v < j, ¬ N2 v := fun v hv => Nat.find_min hN2 hv
  obtain ⟨hjk, hj2, hjnat⟩ := hj
  -- The end of the first block.
  let Pc : ℕ → Prop := fun v => j ≤ v ∧ v ≤ k ∧
    (v = k ∨ ∃ hv : v + 1 < k + 1, ¬ naturalRel D ⟨v - 1, by lia⟩ ⟨v + 1, hv⟩)
  have hPc : ∃ v, Pc v := ⟨k, by lia, le_rfl, Or.inl rfl⟩
  let c := Nat.find hPc
  have hc : Pc c := Nat.find_spec hPc
  have hcmin : ∀ v < c, ¬ Pc v := fun v hv => Nat.find_min hPc hv
  obtain ⟨hjc, hck, hcend⟩ := hc
  -- Length-two edges inside the block.
  have hblock2 : ∀ v (hv : v < k + 1), j ≤ v → v ≤ c → naturalRel D ⟨v - 2, by lia⟩ ⟨v, hv⟩ := by
    intro v hv hjv hvc
    rcases lt_or_eq_of_le hjv with hjv | rfl
    · have := hcmin (v - 1) (by lia)
      simp only [Pc, not_and, not_or, not_exists, not_not] at this
      have h1 := (this (by lia) (by lia)).2 (by lia)
      have ea : (⟨v - 1 - 1, by lia⟩ : Fin (k + 1)) = ⟨v - 2, by lia⟩ :=
        Fin.ext (by show v - 1 - 1 = v - 2; lia)
      have eb : (⟨v - 1 + 1, by lia⟩ : Fin (k + 1)) = ⟨v, hv⟩ :=
        Fin.ext (by show v - 1 + 1 = v; lia)
      rw [ea, eb] at h1
      exact h1
    · exact hjnat
  refine ⟨c, j - 2, hck, by lia, ?_, ?_, ?_, ⟨⟨j - 2, by lia⟩, ⟨j, hjk⟩, hjnat, by simp; lia,
    hjc⟩⟩
  · -- No natural edge crosses `c`.
    intro e he
    by_contra hhead
    rcases hcend with hck' | ⟨hc1, hno⟩
    · have := e.head.isLt
      lia
    · apply hno
      apply naturalRel_sub hD ⟨e, rfl, rfl⟩
      · show e.tail.val ≤ c - 1
        lia
      · show c - 1 < c + 1
        lia
      · show c + 1 ≤ e.head.val
        lia
  · -- The initial path.
    intro u v huv hu
    have hlt : u < v := naturalRel_forward hD huv
    by_contra hne
    have hu2 : u.val + 2 ≤ v.val := by
      have : u.val < v.val := hlt
      lia
    have hN : N2 (u.val + 2) := ⟨by have := v.isLt; lia, by lia,
      naturalRel_sub hD huv (by rw [Fin.le_def]; simp) (by rw [Fin.lt_def]; simp)
        (by rw [Fin.le_def]; simp; lia)⟩
    exact hjmin (u.val + 2) (by lia) hN
  · -- Short edges in the block.
    intro u v hu huv hgap hvc
    have huv' : u.val < v.val := huv
    by_cases hv1 : v.val = u.val + 1
    · exact hadj u v hv1
    · have hv2 : v.val = u.val + 2 := by lia
      have := hblock2 v.val v.isLt (by lia) hvc
      have eu : (⟨v.val - 2, by lia⟩ : Fin (k + 1)) = u := Fin.ext (by show v.val - 2 = u.val; lia)
      rw [eu] at this
      exact this

include hD in
/-- **The attachment step.** In a saturated connected diagram which is not a path,
the witness component has an unmarked certificate by smaller whole components. -/
theorem uCertifies_of_witness (hadj : AdjacentEdges D)
    (hsat : ∀ s t, MaximalPair (naturalRel D) s t → strictRel D s t)
    (hnp : ∃ u v : Fin (k + 1), naturalRel D u v ∧ u.val + 2 ≤ v.val)
    (θ : Orientation D) (hθ : HasCommonWitness θ) :
    ∃ c : Cert k, UCertifies ⟨D, hD, θ⟩ c := by
  obtain ⟨c₀, b, hck, hbc, hcut, hpath, hshort, hnpP⟩ := exists_prefix hD hadj hnp
  obtain ⟨q, rfl⟩ : ∃ q, k = c₀ + q := ⟨k - c₀, by lia⟩
  have h := isRightAttachment_induced (p := c₀) (q := q) hD hcut
  have hP := h.forwardL
  have hT := h.forwardR
  have hblock : InitialPathBlock (inducedDiagram hD (attachLeft c₀ q)) b := by
    refine ⟨?_, ?_, ?_⟩
    · intro u v huv hu
      have := hpath _ _ ((h.natural_left u v).mpr huv) (by simpa using hu)
      simpa using this
    · intro u v hu huv hgap
      exact (h.natural_left u v).mp (hshort _ _ (by simpa using hu)
        ((attachLeft c₀ q).strictMono huv) (by simpa using hgap)
        (by have := v.isLt; simp; lia))
    · intro u v hu huv
      exact (h.natural_left u v).mp (hadj _ _ (by simpa using huv))
  have hnpL : ∃ u v : Fin (c₀ + 1),
      naturalRel (inducedDiagram hD (attachLeft c₀ q)) u v ∧ u.val + 2 ≤ v.val := by
    obtain ⟨u, v, huv, hgap, hvc⟩ := hnpP
    refine ⟨⟨u.val, by lia⟩, ⟨v.val, by lia⟩, (h.natural_left _ _).mp ?_, by simpa using hgap⟩
    have e1 : attachLeft c₀ q ⟨u.val, by lia⟩ = u := Fin.ext rfl
    have e2 : attachLeft c₀ q ⟨v.val, by lia⟩ = v := Fin.ext rfl
    rw [e1, e2]
    exact huv
  obtain ⟨cP, hcP⟩ := certifies_firstDrop hP hblock (h.saturated_left hsat) hnpL
    (h.restrictLeft θ) (h.hasCommonWitness_restrictLeft hθ)
  let hG : ∀ y : Comp c₀, IsRightAttachment (attachDiagram y.D _ y.forward hT) y.D _ :=
    fun y => attachDiagram_isRightAttachment y.D _ y.forward hT
  let glued : Comp c₀ → Comp (c₀ + q) := fun y =>
    ⟨attachDiagram y.D _ y.forward hT, (hG y).forward, (hG y).glue y.θ (h.restrictRight θ)⟩
  have hK (m : ℕ) (β : Fin m) :
      componentMarkedK (h.restrictLeft θ) (Fin.last c₀) m β =
        ∑ y ∈ cP.support, cP y • componentMarkedK y.θ (Fin.last c₀) m β := by
    have := (hcP.1 m β).1
    simp only [Comp.K, Cert.K, Finsupp.linearCombination_apply, Finsupp.sum] at this
    exact this
  have hE (m : ℕ) (β : Fin m) :
      componentMarkedE (h.restrictLeft θ) (Fin.last c₀) m β =
        ∑ y ∈ cP.support, cP y • componentMarkedE y.θ (Fin.last c₀) m β := by
    have := (hcP.1 m β).2
    simp only [Comp.E, Cert.E, Finsupp.linearCombination_apply, Finsupp.sum] at this
    exact this
  refine ⟨∑ y ∈ cP.support, Finsupp.single (glued y) (cP y), fun m => ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨-, -, hKt, -⟩ := attach_transfer cP.support (fun y => cP y) h hG
      (h.restrictLeft θ) (fun y => y.θ) (h.restrictRight θ) m (hK m) (hE m)
    rw [h.glue_restrict] at hKt
    rw [Cert.KU_sum]
    simp only [Cert.KU_single]
    exact hKt
  · obtain ⟨-, -, -, hEt⟩ := attach_transfer cP.support (fun y => cP y) h hG
      (h.restrictLeft θ) (fun y => y.θ) (h.restrictRight θ) m (hK m) (hE m)
    rw [h.glue_restrict] at hEt
    rw [Cert.EU_sum]
    simp only [Cert.EU_single]
    exact hEt
  · exact Cert.smaller_sum fun y hy =>
      Cert.smaller_single (IsRightAttachment.attach_measure_lt h (hG y) (hcP.2 y hy))

end

end VerticalStripLLT.Circular.DiagramProof
