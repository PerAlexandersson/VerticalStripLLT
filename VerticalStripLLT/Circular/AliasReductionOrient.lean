import VerticalStripLLT.Circular.AliasReductionForced
import VerticalStripLLT.Circular.PeriodicSwapHRV
import VerticalStripLLT.Circular.HRVConjugacy

set_option backward.isDefEq.respectTransparency false

/-! The shifted orientation (HRV) identity. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem mem_normalEdges_iff_pair (e : Edge D.area) :
    e ∈ D.edgeData.normalEdges ↔ (e.tail, e.head) ∈ D.pairGraph.normalEdges := by
  change _ ↔ D.endpointEmbedding e ∈ D.edgeData.normalEdges.map D.endpointEmbedding
  rw [Finset.mem_map' D.endpointEmbedding]

theorem edgesOfPairs_map (A : Finset (Edge D.area)) :
    D.edgesOfPairs (A.map D.endpointEmbedding) = A := by
  ext e
  rw [D.mem_edgesOfPairs]
  change D.endpointEmbedding e ∈ A.map D.endpointEmbedding ↔ _
  rw [Finset.mem_map' D.endpointEmbedding]

theorem map_edgesOfPairs {Ap : Finset (Fin n × Fin n)} (h : Ap ⊆ D.pairGraph.normalEdges) :
    (D.edgesOfPairs Ap).map D.endpointEmbedding = Ap := by
  ext x
  rw [Finset.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact (D.mem_edgesOfPairs Ap e).mp he
  · intro hx
    obtain ⟨e, _, hp⟩ := (D.mem_pairGraph_normal_iff x).mp (h hx)
    exact ⟨e, (D.mem_edgesOfPairs Ap e).mpr (by rw [hp]; exact hx), hp⟩

theorem card_edgesOfPairs {Ap : Finset (Fin n × Fin n)} (h : Ap ⊆ D.pairGraph.normalEdges) :
    (D.edgesOfPairs Ap).card = Ap.card := by
  conv_rhs => rw [← D.map_edgesOfPairs h]
  rw [Finset.card_map]

theorem edgesOfPairs_sub_normal {Ap : Finset (Fin n × Fin n)}
    (h : Ap ⊆ D.pairGraph.normalEdges) : D.edgesOfPairs Ap ⊆ D.edgeData.normalEdges := by
  intro e he
  rw [D.mem_normalEdges_iff_pair]
  exact h ((D.mem_edgesOfPairs Ap e).mp he)

theorem edgesOfPairs_mono {Ap Bp : Finset (Fin n × Fin n)} (h : Ap ⊆ Bp) :
    D.edgesOfPairs Ap ⊆ D.edgesOfPairs Bp := by
  intro e he
  rw [D.mem_edgesOfPairs] at he ⊢
  exact h he

/-- A restricted orientation sum over edges with prescribed pairs, as a sum over pair sets. -/
theorem orientSum_edgesOfPairs {S : Finset (Fin n × Fin n)} (hS : S ⊆ D.pairGraph.normalEdges) :
    D.orientSum (D.edgesOfPairs S) = ∑ Ap ∈ S.powerset,
      MvPolynomial.C (Polynomial.X ^ Ap.card) * D.orientMono (D.edgesOfPairs Ap) := by
  unfold orientSum
  apply Finset.sum_nbij' (fun A => A.map D.endpointEmbedding) (fun Ap => D.edgesOfPairs Ap)
  · intro A hA
    rw [Finset.mem_powerset] at hA ⊢
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hx
    exact (D.mem_edgesOfPairs S e).mp (hA he)
  · intro Ap hAp
    rw [Finset.mem_powerset] at hAp ⊢
    exact D.edgesOfPairs_mono hAp
  · intro A _
    exact D.edgesOfPairs_map A
  · intro Ap hAp
    rw [Finset.mem_powerset] at hAp
    exact D.map_edgesOfPairs (hAp.trans hS)
  · intro A _
    rw [Finset.card_map, D.edgesOfPairs_map]

end Diagram

namespace AliasContacts

variable {n : ℕ} {D : Diagram n} (K : AliasContacts D)

theorem RD_sub_ND : K.RD ⊆ D.pairGraph.normalEdges := Finset.sdiff_subset

theorem RQ_sub_NQ : K.RQ ⊆ K.target.pairGraph.normalEdges := Finset.sdiff_subset

theorem not_X_of_RD {x : Fin n × Fin n} (h : x ∈ K.RD) : x ∉ K.Xset :=
  (Finset.mem_sdiff.mp h).2

theorem not_XQ_of_RQ {x : Fin n × Fin n} (h : x ∈ K.RQ) : x ∉ K.XQset :=
  (Finset.mem_sdiff.mp h).2

noncomputable def σE : ℤ ≃ ℤ := Function.Involutive.toPerm K.σ K.σ_involutive

theorem σE_apply (z : ℤ) : K.σE z = K.σ z := rfl

section Transport

variable (Ap : Finset (Fin n × Fin n)) (hAp : Ap ⊆ K.RD)

include hAp in
theorem transport_step (x y : ℤ) :
    D.liftStep (D.edgesOfPairs Ap) x y ↔
      K.target.liftStep (K.target.edgesOfPairs (Ap.map K.π2)) (K.σ x) (K.σ y) := by
  rw [D.liftStep_edgesOfPairs_iff, K.target.liftStep_edgesOfPairs_iff, K.target_residue,
    ← K.π2_res, Finset.mem_map' K.π2, K.strict_lift_conjugacy x y]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hX := K.not_X_of_RD (hAp h3)
    obtain ⟨a, b, _⟩ := (K.exterior_lift_conjugacy x y).mp ⟨h1, h2, hX⟩
    exact ⟨a, b, h3⟩
  · rintro ⟨h1, h2, h3⟩
    have hXQ : (D.residue (K.σ x), D.residue (K.σ y)) ∉ K.XQset := by
      rw [← K.π2_res]
      apply K.not_XQ_of_RQ
      rw [K.RQ_eq]
      exact Finset.mem_map_of_mem _ (hAp h3)
    obtain ⟨a, b, _⟩ := (K.exterior_lift_conjugacy x y).mpr ⟨h1, h2, hXQ⟩
    exact ⟨a, b, h3⟩

include hAp in
theorem transport_transGen_fwd {z w : ℤ}
    (h : Relation.TransGen (D.liftStep (D.edgesOfPairs Ap)) z w) :
    Relation.TransGen (K.target.liftStep (K.target.edgesOfPairs (Ap.map K.π2)))
      (K.σ z) (K.σ w) :=
  Relation.TransGen.lift K.σ (fun a b hab => (K.transport_step Ap hAp a b).mp hab) _ _ h

include hAp in
theorem transport_transGen_bwd {z w : ℤ}
    (h : Relation.TransGen (K.target.liftStep (K.target.edgesOfPairs (Ap.map K.π2))) z w) :
    Relation.TransGen (D.liftStep (D.edgesOfPairs Ap)) (K.σ z) (K.σ w) :=
  Relation.TransGen.lift K.σ (fun a b hab => (K.transport_step Ap hAp (K.σ a) (K.σ b)).mpr
    (by simpa using hab)) _ _ h

include hAp in
theorem transport_admissible :
    D.edgeData.Admissible (D.edgesOfPairs Ap) ↔
      K.target.edgeData.Admissible (K.target.edgesOfPairs (Ap.map K.π2)) := by
  rw [D.admissible_iff_lift, K.target.admissible_iff_lift, K.target_residue]
  constructor
  · intro h z w hzw heq
    have := h _ _ (K.transport_transGen_bwd Ap hAp hzw)
    rw [K.res_σ, K.res_σ, heq] at this
    exact this rfl
  · intro h z w hzw heq
    have := h _ _ (K.transport_transGen_fwd Ap hAp hzw)
    rw [K.res_σ, K.res_σ, heq] at this
    exact this rfl

theorem exists_out_of_L (A : Finset (Edge D.area)) {z : ℤ} (hz : z ∈ K.L) :
    ∃ w, D.liftStep A z w := by
  obtain ⟨j, hj, hres⟩ := hz
  obtain ⟨h, rfl⟩ := D.residue_eq_exists_period hres
  by_cases hjr : j + 1 < K.r
  · obtain ⟨e, he, heh, het⟩ := D.strictAt_edge (K.strictP (j + 1) (by lia) hjr)
    refine ⟨K.P (j + 1) + (n : ℤ) * h, e, Finset.mem_union_left _ he, ?_, ?_⟩
    · rw [D.residue_add_period, het, K.bP j hjr]
    · rw [(D.strict_corner e he).1, heh]
      have := K.bP j hjr
      unfold Diagram.boundary at this
      lia
  · have hj' : j = K.r - 1 := by lia
    subst hj'
    obtain ⟨e, he, heh, het⟩ := D.strictAt_edge K.strict_t
    refine ⟨K.t + (n : ℤ) * h, e, Finset.mem_union_left _ he, ?_, ?_⟩
    · rw [D.residue_add_period, het, K.bt]
    · rw [(D.strict_corner e he).1, heh]
      have := K.bt
      unfold Diagram.boundary at this
      lia

theorem sink_order (A : Finset (Edge D.area)) :
    ∀ x y, (∀ z, ¬ D.liftStep A x z) → (∀ z, ¬ D.liftStep A y z) → x ≤ y →
      K.σE x ≤ K.σE y := by
  let T : Set ℤ := {x | ∀ z, ¬ D.liftStep A x z}
  have hsep : ∀ z ∈ K.L, ¬ (z ∈ T ∧ z + 1 ∈ T) := by
    intro z hz ⟨hT, _⟩
    obtain ⟨w, hw⟩ := K.exists_out_of_L A hz
    exact hT w hw
  have hmono := adjacentSwap_strictMonoOn K.L T K.L_sep hsep
  intro x y hx hy hxy
  rcases hxy.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (hmono hx hy hlt).le

include hAp in
theorem transport_orientMono :
    D.orientMono (D.edgesOfPairs Ap) =
      K.target.orientMono (K.target.edgesOfPairs (Ap.map K.π2)) := by
  have hA : D.edgesOfPairs Ap ⊆ D.edgeData.normalEdges :=
    D.edgesOfPairs_sub_normal (hAp.trans K.RD_sub_ND)
  have hA' : K.target.edgesOfPairs (Ap.map K.π2) ⊆ K.target.edgeData.normalEdges := by
    apply K.target.edgesOfPairs_sub_normal
    rw [← Finset.map_subset_map (f := K.π2)] at hAp
    rw [← K.RQ_eq] at hAp
    exact hAp.trans K.RQ_sub_NQ
  have hadm := K.transport_admissible Ap hAp
  apply D.orientMono_eq_of _ _ hA hA'
  · intro h
    refine ⟨hadm.mp h, fun h' => ?_⟩
    apply Orientation.hrvMonomial_conjugate _ _ K.π
    apply Orientation.hrv_conjugate _ _ K.σE K.π
    · intro x
      rw [K.σE_apply, K.target_residue, K.res_σ]
    · intro x y
      exact K.transport_step Ap hAp x y
    · exact K.sink_order _
  · exact hadm.mpr

end Transport

/-! Assembling the orientation expansions. -/

theorem orient_source :
    shiftedOrientationExpansion D = MvPolynomial.C (Polynomial.X + 1) ^ K.r *
      D.orientSum (D.edgesOfPairs K.RD) := by
  rw [D.shiftedOrientationExpansion_eq_orientSum]
  have hBsub : D.edgesOfPairs K.Bset ⊆ D.edgeData.normalEdges :=
    D.edgesOfPairs_sub_normal K.B_sub_ND
  rw [D.orientSum_forced_set _ _ (Finset.Subset.refl _) hBsub (by
    intro e he
    exact D.transGen_selected_of_pairs (K.B_path_D _ ((D.mem_edgesOfPairs _ e).mp he)))]
  rw [D.card_edgesOfPairs K.B_sub_ND, K.card_B]
  have hCH : D.edgesOfPairs (K.Cset ∪ K.Hset) ⊆ D.edgeData.normalEdges \ D.edgesOfPairs K.Bset := by
    intro e he
    rw [D.mem_edgesOfPairs] at he
    rw [Finset.mem_sdiff, D.mem_edgesOfPairs, D.mem_normalEdges_iff_pair]
    refine ⟨Finset.union_subset K.C_sub_ND K.H_sub_ND he, fun hB => ?_⟩
    exact Finset.disjoint_left.mp K.disjoint_B_CH hB he
  rw [D.orientSum_descent_set _ _ hCH (by
    intro e he
    exact D.transGen_selected_of_pairs (K.CH_path_D _ ((D.mem_edgesOfPairs _ e).mp he)))]
  congr 2
  ext e
  simp only [Finset.mem_sdiff, D.mem_edgesOfPairs, D.mem_normalEdges_iff_pair, RD, Xset,
    XQset, Finset.mem_union]
  tauto

theorem orient_target :
    shiftedOrientationExpansion K.target = MvPolynomial.C (Polynomial.X + 1) ^ (K.r - 1) *
      K.target.orientSum (K.target.edgesOfPairs K.RQ) := by
  rw [K.target.shiftedOrientationExpansion_eq_orientSum]
  have hCsub : K.target.edgesOfPairs K.Cset ⊆ K.target.edgeData.normalEdges :=
    K.target.edgesOfPairs_sub_normal K.C_sub_NQ
  rw [K.target.orientSum_forced_set _ _ (Finset.Subset.refl _) hCsub (by
    intro e he
    exact K.target.transGen_selected_of_pairs
      (K.C_path_Q _ ((K.target.mem_edgesOfPairs _ e).mp he)))]
  rw [K.target.card_edgesOfPairs K.C_sub_NQ, K.card_C]
  have hB : K.target.edgesOfPairs K.Bset ⊆
      K.target.edgeData.normalEdges \ K.target.edgesOfPairs K.Cset := by
    intro e he
    rw [K.target.mem_edgesOfPairs] at he
    rw [Finset.mem_sdiff, K.target.mem_edgesOfPairs, K.target.mem_normalEdges_iff_pair]
    exact ⟨K.B_sub_NQ he, fun hC => Finset.disjoint_left.mp K.disjoint_C_B hC he⟩
  rw [K.target.orientSum_descent_set _ _ hB (by
    intro e he
    exact K.target.transGen_selected_of_pairs
      (K.B_path_Q _ ((K.target.mem_edgesOfPairs _ e).mp he)))]
  congr 2
  ext e
  simp only [Finset.mem_sdiff, K.target.mem_edgesOfPairs, K.target.mem_normalEdges_iff_pair,
    RQ, XQset, Finset.mem_union]
  tauto

theorem orientSum_transport :
    D.orientSum (D.edgesOfPairs K.RD) = K.target.orientSum (K.target.edgesOfPairs K.RQ) := by
  rw [D.orientSum_edgesOfPairs K.RD_sub_ND, K.target.orientSum_edgesOfPairs K.RQ_sub_NQ,
    K.RQ_eq]
  apply Finset.sum_nbij' (fun Ap => Ap.map K.π2)
    (fun Ap' => Ap'.map (Equiv.prodCongr K.π K.π).symm.toEmbedding)
  · intro Ap hAp
    rw [Finset.mem_powerset] at hAp ⊢
    exact Finset.map_subset_map.mpr hAp
  · intro Ap' hAp'
    rw [Finset.mem_powerset] at hAp' ⊢
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp (hAp' hy)
    obtain ⟨a, b⟩ := z
    simpa [π2] using hz
  · intro Ap _
    ext ⟨a, b⟩
    simp [π2]
  · intro Ap' _
    ext ⟨a, b⟩
    simp [π2]
  · intro Ap hAp
    rw [Finset.mem_powerset] at hAp
    rw [Finset.card_map, K.transport_orientMono Ap hAp]

theorem orient_identity :
    shiftedOrientationExpansion D =
      MvPolynomial.C (Polynomial.X + 1) * shiftedOrientationExpansion K.target := by
  rw [K.orient_source, K.orient_target, K.orientSum_transport, ← mul_assoc, ← pow_succ']
  congr 2
  have := K.two_le
  lia

end AliasContacts

end VerticalStripLLT.Circular
