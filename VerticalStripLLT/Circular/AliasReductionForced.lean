import VerticalStripLLT.Circular.AliasReductionPairs

set_option backward.isDefEq.respectTransparency false

/-! Forced ascents and descents along the concatenated strict chains, and the
coloring identity. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

theorem transGen_of_chain {α : Type*} (R : α → α → Prop) (w : ℕ → α) (M : ℕ)
    (h : ∀ i, i + 1 < M → R (w i) (w (i + 1))) :
    ∀ a b, a < b → b < M → Relation.TransGen R (w a) (w b) := by
  intro a b
  induction b with
  | zero => intro h; lia
  | succ b ih =>
    intro hab hbM
    by_cases hab' : a = b
    · subst hab'; exact Relation.TransGen.single (h a hbM)
    · exact Relation.TransGen.tail (ih (by lia) (by lia)) (h b hbM)

namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem transGen_selected_of_pairs {a b : Fin n}
    (h : Relation.TransGen (fun x y => (x, y) ∈ D.pairGraph.strictEdges) a b) :
    Relation.TransGen (D.edgeData.selected ∅) a b := by
  refine Relation.TransGen.mono (fun x y hxy => ?_) _ _ h
  obtain ⟨e, he, hp⟩ := (D.mem_pairGraph_strict_iff _).mp hxy
  exact ⟨e, by simpa [Diagram.edgeData] using he, congrArg Prod.fst hp,
    congrArg Prod.snd hp⟩

end Diagram

namespace AliasContacts

variable {n : ℕ} {D : Diagram n} (K : AliasContacts D)

theorem pair_pp (i : ℕ) (hi : i + 1 < K.r) : (K.p i, K.p (i + 1)) ∈ D.pairGraph.strictEdges :=
  (D.mem_strict_pairs_iff _ _).mpr
    ⟨K.P i, K.P (i + 1), rfl, rfl, K.strictP (i + 1) (by lia) hi, (K.bP i hi).symm⟩

theorem pair_qq (i : ℕ) (hi : i + 1 < K.r) : (K.q i, K.q (i + 1)) ∈ D.pairGraph.strictEdges :=
  (D.mem_strict_pairs_iff _ _).mpr
    ⟨K.P i + 1, K.P (i + 1) + 1, rfl, rfl, K.strictQ (i + 1) hi, (K.bQ i hi).symm⟩

theorem pair_pq : (K.p (K.r - 1), K.q 0) ∈ D.pairGraph.strictEdges :=
  (D.mem_strict_pairs_iff _ _).mpr ⟨K.P (K.r - 1), K.t, rfl, K.res_t, K.strict_t, K.bt.symm⟩

/-- The source strict chain `p_0 → ⋯ → p_last → q_0 → ⋯ → q_last`. -/
def wD (i : ℕ) : Fin n := if i < K.r then K.p i else K.q (i - K.r)

/-- The target strict chain `q_0 → ⋯ → q_last → p_0 → ⋯ → p_last`. -/
def wQ (i : ℕ) : Fin n := if i < K.r then K.q i else K.p (i - K.r)

theorem wD_lo (j : ℕ) (hj : j < K.r) : K.wD j = K.p j := by simp [wD, hj]

theorem wD_hi (j : ℕ) : K.wD (K.r + j) = K.q j := by simp [wD]

theorem wQ_lo (j : ℕ) (hj : j < K.r) : K.wQ j = K.q j := by simp [wQ, hj]

theorem wQ_hi (j : ℕ) : K.wQ (K.r + j) = K.p j := by simp [wQ]

theorem wD_step (i : ℕ) (hi : i + 1 < 2 * K.r) :
    (K.wD i, K.wD (i + 1)) ∈ D.pairGraph.strictEdges := by
  by_cases h1 : i + 1 < K.r
  · rw [K.wD_lo i (by lia), K.wD_lo (i + 1) h1]; exact K.pair_pp i h1
  by_cases h2 : i + 1 = K.r
  · rw [K.wD_lo i (by lia), show i + 1 = K.r + 0 by lia, K.wD_hi,
      show i = K.r - 1 by lia]
    exact K.pair_pq
  · obtain ⟨j, rfl⟩ : ∃ j, i = K.r + j := ⟨i - K.r, by lia⟩
    rw [K.wD_hi, show K.r + j + 1 = K.r + (j + 1) by ring, K.wD_hi]
    exact K.pair_qq j (by lia)

theorem wQ_step (i : ℕ) (hi : i + 1 < 2 * K.r) :
    (K.wQ i, K.wQ (i + 1)) ∈ K.target.pairGraph.strictEdges := by
  rw [K.target_strict_pairs, Finset.mem_map]
  refine ⟨(K.wD i, K.wD (i + 1)), K.wD_step i hi, ?_⟩
  rw [K.π2_apply]
  by_cases h1 : i + 1 < K.r
  · rw [K.wD_lo i (by lia), K.wD_lo (i + 1) h1, K.wQ_lo i (by lia), K.wQ_lo (i + 1) h1,
      K.π_p i (by lia), K.π_p (i + 1) h1]
  by_cases h2 : i + 1 = K.r
  · rw [K.wD_lo i (by lia), K.wQ_lo i (by lia), show i + 1 = K.r + 0 by lia, K.wD_hi,
      K.wQ_hi, K.π_p i (by lia), K.π_q 0 K.r_pos]
  · obtain ⟨j, rfl⟩ : ∃ j, i = K.r + j := ⟨i - K.r, by lia⟩
    rw [K.wD_hi, K.wQ_hi, show K.r + j + 1 = K.r + (j + 1) by ring, K.wD_hi, K.wQ_hi,
      K.π_q j (by lia), K.π_q (j + 1) (by lia)]

theorem pathD {a b : ℕ} (hab : a < b) (hb : b < 2 * K.r) :
    Relation.TransGen (fun x y => (x, y) ∈ D.pairGraph.strictEdges) (K.wD a) (K.wD b) :=
  transGen_of_chain _ K.wD (2 * K.r) (fun i hi => K.wD_step i hi) a b hab hb

theorem pathQ {a b : ℕ} (hab : a < b) (hb : b < 2 * K.r) :
    Relation.TransGen (fun x y => (x, y) ∈ K.target.pairGraph.strictEdges)
      (K.wQ a) (K.wQ b) :=
  transGen_of_chain _ K.wQ (2 * K.r) (fun i hi => K.wQ_step i hi) a b hab hb

theorem B_path_D (x : Fin n × Fin n) (hx : x ∈ K.Bset) :
    Relation.TransGen (fun x y => (x, y) ∈ D.pairGraph.strictEdges) x.1 x.2 := by
  obtain ⟨j, hj, rfl⟩ := (K.mem_Bset x).mp hx
  have := K.pathD (a := j) (b := K.r + j) (by lia) (by lia)
  rwa [K.wD_lo j hj, K.wD_hi] at this

theorem CH_path_D (x : Fin n × Fin n) (hx : x ∈ K.Cset ∪ K.Hset) :
    Relation.TransGen (fun x y => (x, y) ∈ D.pairGraph.strictEdges) x.2 x.1 := by
  have h2 := K.two_le
  rcases Finset.mem_union.mp hx with hC | hH
  · obtain ⟨j, h1, hj, rfl⟩ := (K.mem_Cset x).mp hC
    have := K.pathD (a := j) (b := K.r + (j - 1)) (by lia) (by lia)
    rwa [K.wD_lo j hj, K.wD_hi] at this
  · obtain ⟨a, b⟩ := x
    rcases (K.mem_Hset a b).mp hH with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
    · have := K.pathD (a := 0) (b := K.r - 1) (by lia) (by lia)
      rwa [K.wD_lo 0 (by lia), K.wD_lo (K.r - 1) (by lia)] at this
    · have := K.pathD (a := 0) (b := K.r + (K.r - 1)) (by lia) (by lia)
      rwa [K.wD_lo 0 (by lia), K.wD_hi] at this
    · have := K.pathD (a := K.r + 0) (b := K.r + (K.r - 1)) (by lia) (by lia)
      rwa [K.wD_hi, K.wD_hi] at this

theorem C_path_Q (x : Fin n × Fin n) (hx : x ∈ K.Cset) :
    Relation.TransGen (fun x y => (x, y) ∈ K.target.pairGraph.strictEdges) x.1 x.2 := by
  obtain ⟨j, h1, hj, rfl⟩ := (K.mem_Cset x).mp hx
  have := K.pathQ (a := j - 1) (b := K.r + j) (by lia) (by lia)
  rwa [K.wQ_lo (j - 1) (by lia), K.wQ_hi] at this

theorem B_path_Q (x : Fin n × Fin n) (hx : x ∈ K.Bset) :
    Relation.TransGen (fun x y => (x, y) ∈ K.target.pairGraph.strictEdges) x.2 x.1 := by
  obtain ⟨j, hj, rfl⟩ := (K.mem_Bset x).mp hx
  have := K.pathQ (a := j) (b := K.r + j) (by lia) (by lia)
  rwa [K.wQ_lo j hj, K.wQ_hi] at this

/-! Exceptional pairs are normal pairs. -/

theorem B_sub_ND : K.Bset ⊆ D.pairGraph.normalEdges := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := (K.mem_Bset x).mp hx
  rw [D.mem_normal_pairs_iff]
  refine ⟨K.P j, K.P j + 1, rfl, rfl, ?_, by lia, ?_⟩
  · rcases j with _ | i
    · rw [K.b0]; exact D.boundary_le_self _
    · rw [K.bQ i hj]; have := K.P_add_two_le i hj; lia
  · rintro ⟨_, h⟩
    rcases j with _ | i
    · rw [K.b0] at h; have := K.β_add_two_le; unfold β at this; lia
    · rw [K.bQ i hj] at h; have := K.P_add_two_le i hj; lia

theorem C_sub_ND : K.Cset ⊆ D.pairGraph.normalEdges := by
  intro x hx
  obtain ⟨j, h1, hj, rfl⟩ := (K.mem_Cset x).mp hx
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by lia⟩
  rw [D.mem_normal_pairs_iff]
  have h2 := K.P_add_two_le i hj
  refine ⟨K.P i + 1, K.P (i + 1), rfl, rfl, ?_, by lia, ?_⟩
  · rw [K.bP i hj]; lia
  · rintro ⟨_, h⟩; rw [K.bP i hj] at h; lia

theorem H_sub_ND : K.Hset ⊆ D.pairGraph.normalEdges := by
  intro x hx
  obtain ⟨a, b⟩ := x
  have h2 := K.β_add_two_le
  have hβ : K.β = D.boundary (K.P 0) := rfl
  rw [D.mem_normal_pairs_iff]
  rcases (K.mem_Hset a b).mp hx with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨K.β, K.P 0, K.res_β, rfl, le_of_eq hβ.symm, by lia, ?_⟩
    rintro ⟨h, _⟩; exact K.notStrict0 h
  · refine ⟨K.β + 1, K.P 0, K.res_β1, rfl, by lia, by lia, ?_⟩
    rintro ⟨h, _⟩; exact K.notStrict0 h
  · refine ⟨K.β + 1, K.P 0 + 1, K.res_β1, rfl, by rw [K.b0]; lia, by lia, ?_⟩
    rintro ⟨_, h⟩; rw [K.b0] at h; lia

theorem B_sub_NQ : K.Bset ⊆ K.target.pairGraph.normalEdges := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := (K.mem_Bset x).mp hx
  rw [K.target.mem_normal_pairs_iff, K.target_residue]
  refine ⟨K.P j, K.P j + 1, rfl, rfl, ?_, by lia, ?_⟩
  · rcases j with _ | i
    · rw [K.target_boundary_q0 rfl, K.b0]; have := K.β_add_two_le; unfold β at this; lia
    · rw [K.target_boundary_other (K.q_succ_ne_p0 i hj) (K.q_succ_ne_q0 i hj), K.bQ i hj]
      have := K.P_add_two_le i hj; lia
  · rintro ⟨hs, h⟩
    rcases j with _ | i
    · rw [K.target_strictAt_iff] at hs
      rcases hs with hs | ⟨_, hs⟩
      · exact K.p0_ne_q0 hs.symm
      · exact hs rfl
    · rw [K.target_boundary_other (K.q_succ_ne_p0 i hj) (K.q_succ_ne_q0 i hj), K.bQ i hj] at h
      have := K.P_add_two_le i hj; lia

theorem C_sub_NQ : K.Cset ⊆ K.target.pairGraph.normalEdges := by
  intro x hx
  obtain ⟨j, h1, hj, rfl⟩ := (K.mem_Cset x).mp hx
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by lia⟩
  rw [K.target.mem_normal_pairs_iff, K.target_residue]
  have h2 := K.P_add_two_le i hj
  have hb : K.target.boundary (K.P (i + 1)) = K.P i := by
    rw [K.target_boundary_other (K.p_succ_ne_p0 i hj) (K.p_succ_ne_q0 i hj), K.bP i hj]
  refine ⟨K.P i + 1, K.P (i + 1), rfl, rfl, ?_, by lia, ?_⟩
  · rw [hb]; lia
  · rintro ⟨_, h⟩; rw [hb] at h; lia

/-! Disjointness and cardinalities. -/

theorem disjoint_B_CH : Disjoint K.Bset (K.Cset ∪ K.Hset) := by
  rw [Finset.disjoint_left]
  intro x hxB hx
  obtain ⟨j, hj, rfl⟩ := (K.mem_Bset x).mp hxB
  rcases Finset.mem_union.mp hx with hC | hH
  · obtain ⟨i, _, hi, h⟩ := (K.mem_Cset _).mp hC
    exact K.p_ne_q hj (by lia) (congrArg Prod.fst h)
  · rcases (K.mem_Hset _ _).mp hH with ⟨h, _⟩ | ⟨h, h'⟩
    · exact K.p_ne_q K.r_pos hj h.symm
    · have := K.q_inj hj K.r_pos h
      subst this
      exact K.p_ne_q K.r_pos K.last_lt h'

theorem disjoint_C_B : Disjoint K.Cset K.Bset := by
  rw [Finset.disjoint_left]
  intro x hxC hxB
  exact Finset.disjoint_left.mp K.disjoint_B_CH hxB (Finset.mem_union_left _ hxC)

theorem card_B : K.Bset.card = K.r := by
  unfold Bset
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj h
  exact K.p_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (congrArg Prod.fst h)

theorem card_C : K.Cset.card = K.r - 1 := by
  unfold Cset
  rw [Finset.card_image_of_injOn, Nat.card_Ico]
  intro i hi j hj h
  exact K.p_inj (Finset.mem_Ico.mp hi).2 (Finset.mem_Ico.mp hj).2 (congrArg Prod.snd h)

/-! The coloring identity. -/

theorem coloring_source (m : ℕ) : D.coloringLLT m = MvPolynomial.C Polynomial.X ^ K.r *
    (⟨K.RD, D.pairGraph.strictEdges⟩ : PairGraph n).coloringLLT m := by
  rw [← D.pairGraph_coloringLLT, PairGraph.coloringLLT_erase_forced_set D.pairGraph K.Bset
    K.B_sub_ND K.B_path_D, PairGraph.coloringLLT_erase_descent_set
    (⟨D.pairGraph.normalEdges \ K.Bset, D.pairGraph.strictEdges⟩ : PairGraph n)
    (K.Cset ∪ K.Hset) K.CH_path_D, K.card_B]
  congr 3
  change (D.pairGraph.normalEdges \ K.Bset) \ (K.Cset ∪ K.Hset) = K.RD
  rw [sdiff_sdiff_left, RD, Xset, XQset, Finset.union_assoc]
  rfl

theorem coloring_target (m : ℕ) : K.target.coloringLLT m =
    MvPolynomial.C Polynomial.X ^ (K.r - 1) *
      (⟨K.RD, D.pairGraph.strictEdges⟩ : PairGraph n).coloringLLT m := by
  rw [← K.target.pairGraph_coloringLLT, PairGraph.coloringLLT_erase_forced_set
    K.target.pairGraph K.Cset K.C_sub_NQ K.C_path_Q, PairGraph.coloringLLT_erase_descent_set
    (⟨K.target.pairGraph.normalEdges \ K.Cset, K.target.pairGraph.strictEdges⟩ : PairGraph n)
    K.Bset K.B_path_Q, K.card_C]
  congr 1
  have hR : (K.target.pairGraph.normalEdges \ K.Cset) \ K.Bset = K.RD.map K.π2 := by
    rw [← K.RQ_eq, RQ, XQset, sdiff_sdiff_left, Finset.union_comm]
    rfl
  simp only [hR, K.target_strict_pairs]
  exact PairGraph.coloringLLT_relabel K.π K.RD D.pairGraph.strictEdges

theorem coloring_identity (m : ℕ) :
    D.coloringLLT m = MvPolynomial.C Polynomial.X * K.target.coloringLLT m := by
  rw [K.coloring_source, K.coloring_target, ← mul_assoc, ← pow_succ']
  congr 3
  have := K.two_le
  lia

end AliasContacts

end VerticalStripLLT.Circular
