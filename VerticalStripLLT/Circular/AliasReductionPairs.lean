import VerticalStripLLT.Circular.AliasReductionRelations

set_option backward.isDefEq.respectTransparency false

/-! Endpoint-pair consequences of the lifted conjugacy. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem mem_strict_pairs_iff (a b : Fin n) :
    (a, b) ∈ D.pairGraph.strictEdges ↔
      ∃ u v : ℤ, D.residue u = a ∧ D.residue v = b ∧ D.strictAt v ∧ u = D.boundary v := by
  constructor
  · intro h
    obtain ⟨e, he, hp⟩ := (D.mem_pairGraph_strict_iff _).mp h
    obtain ⟨ht, hh⟩ := Prod.mk.inj hp
    refine ⟨D.boundary (e.head.val : ℤ), (e.head.val : ℤ), ?_, ?_, ⟨e, he, ?_⟩, rfl⟩
    · rw [← D.strictEdge_tail_boundary he, ht]
    · rw [Orientation.residue_intCast_eq, hh]
    · rw [Orientation.residue_intCast_eq]
  · rintro ⟨u, v, rfl, rfl, hs, rfl⟩
    obtain ⟨e, he, hh, ht⟩ := D.strictAt_edge hs
    exact (D.mem_pairGraph_strict_iff _).mpr ⟨e, he, by rw [hh, ht]⟩

theorem mem_normal_pairs_iff (a b : Fin n) :
    (a, b) ∈ D.pairGraph.normalEdges ↔
      ∃ u v : ℤ, D.residue u = a ∧ D.residue v = b ∧ D.boundary v ≤ u ∧ u < v ∧
        ¬ (D.strictAt v ∧ u = D.boundary v) := by
  constructor
  · intro h
    obtain ⟨e, he, hp⟩ := (D.mem_pairGraph_normal_iff _).mp h
    obtain ⟨ht, hh⟩ := Prod.mk.inj hp
    have hns : e ∉ D.strict := (D.mem_normalEdges_iff e).mp he
    obtain ⟨v, hv⟩ : ∃ v : ℤ, v = (e.head.val : ℤ) := ⟨_, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u : ℤ, u = v - e.length.val := ⟨_, rfl⟩
    have hhv : e.head = D.residue v := by
      rw [hv]
      exact (Orientation.residue_intCast_eq e.head).symm
    have hlen : (e.length.val : ℤ) = v - u := by rw [hu]; ring
    have hl := D.boundaryNaturalLift_of_edge hhv hlen
    refine ⟨u, v, ?_, ?_, hl.1, hl.2, ?_⟩
    · rw [← D.residue_tail_of_length hhv hlen, ht]
    · rw [← hhv, hh]
    · rintro hsv
      have := (D.edgeFromLift_mem_strict_iff hl).mpr hsv
      have heq : D.edgeFromLift u v hl = e := by
        apply D.edge_eq_of_endpoints
        · rw [D.edgeFromLift_tail, D.residue_tail_of_length hhv hlen]
        · rw [D.edgeFromLift_head, hhv]
      exact hns (heq ▸ this)
  · rintro ⟨u, v, rfl, rfl, hb, huv, hns⟩
    have hl : D.boundaryNaturalLift u v := ⟨hb, huv⟩
    refine (D.mem_pairGraph_normal_iff _).mpr ⟨D.edgeFromLift u v hl, ?_, ?_⟩
    · rw [D.mem_normalEdges_iff, D.edgeFromLift_mem_strict_iff]
      exact hns
    · rw [D.edgeFromLift_tail, D.edgeFromLift_head]

end Diagram

namespace AliasContacts

variable {n : ℕ} {D : Diagram n} (K : AliasContacts D)

theorem p_injective : Function.Injective (fun i : Fin K.r => K.p i.val) := by
  intro i j h
  exact Fin.ext (K.p_inj i.isLt j.isLt h)

theorem q_injective : Function.Injective (fun i : Fin K.r => K.q i.val) := by
  intro i j h
  exact Fin.ext (K.q_inj i.isLt j.isLt h)

/-- The residue action of the simultaneous swap. -/
noncomputable def π : Equiv.Perm (Fin n) :=
  pairedSwap (fun i : Fin K.r => K.p i.val) (fun i : Fin K.r => K.q i.val)
    K.p_injective K.q_injective (fun i j => K.p_ne_q i.isLt j.isLt)

theorem π_p (j : ℕ) (hj : j < K.r) : K.π (K.p j) = K.q j :=
  pairedSwap_left (fun i : Fin K.r => K.p i.val) (fun i : Fin K.r => K.q i.val)
    K.p_injective K.q_injective (fun i j => K.p_ne_q i.isLt j.isLt) ⟨j, hj⟩

theorem π_q (j : ℕ) (hj : j < K.r) : K.π (K.q j) = K.p j :=
  pairedSwap_right (fun i : Fin K.r => K.p i.val) (fun i : Fin K.r => K.q i.val)
    K.p_injective K.q_injective (fun i j => K.p_ne_q i.isLt j.isLt) ⟨j, hj⟩

theorem π_fix (v : Fin n) (hv : ∀ j < K.r, v ≠ K.p j ∧ v ≠ K.q j) : K.π v = v :=
  pairedSwap_fixed (fun i : Fin K.r => K.p i.val) (fun i : Fin K.r => K.q i.val)
    K.p_injective K.q_injective (fun i j => K.p_ne_q i.isLt j.isLt) v
    (fun i => (hv i.val i.isLt).1) (fun i => (hv i.val i.isLt).2)

theorem res_σ (z : ℤ) : D.residue (K.σ z) = K.π (D.residue z) := by
  rcases K.classify z with ⟨j, hj, h, rfl⟩ | ⟨j, hj, h, rfl⟩ | hv
  · rw [K.σ_translate, K.σ_P j hj, D.residue_add_period, D.residue_add_period]
    exact (K.π_p j hj).symm
  · rw [K.σ_translate, K.σ_P1 j hj, D.residue_add_period, D.residue_add_period]
    exact (K.π_q j hj).symm
  · rw [K.σ_ext z hv, K.π_fix _ hv]

/-- The swap acting on endpoint pairs. -/
noncomputable def π2 : (Fin n × Fin n) ↪ (Fin n × Fin n) :=
  (Equiv.prodCongr K.π K.π).toEmbedding

theorem π2_apply (x : Fin n × Fin n) : K.π2 x = (K.π x.1, K.π x.2) := rfl

theorem π2_res (u v : ℤ) :
    K.π2 (D.residue u, D.residue v) = (D.residue (K.σ u), D.residue (K.σ v)) := by
  rw [π2_apply, K.res_σ, K.res_σ]

theorem target_strict_pairs :
    K.target.pairGraph.strictEdges = D.pairGraph.strictEdges.map K.π2 := by
  ext ⟨a', b'⟩
  rw [K.target.mem_strict_pairs_iff, Finset.mem_map, K.target_residue]
  constructor
  · rintro ⟨u', v', rfl, rfl, hs⟩
    refine ⟨(D.residue (K.σ u'), D.residue (K.σ v')), ?_, ?_⟩
    · rw [D.mem_strict_pairs_iff]
      refine ⟨K.σ u', K.σ v', rfl, rfl, ?_⟩
      rw [K.strict_lift_conjugacy, K.σ_σ, K.σ_σ]
      exact hs
    · rw [K.π2_res, K.σ_σ, K.σ_σ]
  · rintro ⟨⟨a, b⟩, hab, heq⟩
    obtain ⟨u, v, rfl, rfl, hs⟩ := (D.mem_strict_pairs_iff a b).mp hab
    rw [K.π2_res] at heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨K.σ u, K.σ v, rfl, rfl, (K.strict_lift_conjugacy u v).mp hs⟩

/-- Remaining source normal pairs. -/
noncomputable def RD : Finset (Fin n × Fin n) := D.pairGraph.normalEdges \ K.Xset

/-- Remaining target normal pairs. -/
noncomputable def RQ : Finset (Fin n × Fin n) := K.target.pairGraph.normalEdges \ K.XQset

theorem mem_RD_iff (a b : Fin n) : (a, b) ∈ K.RD ↔
    ∃ u v : ℤ, D.residue u = a ∧ D.residue v = b ∧
      (D.boundary v ≤ u ∧ u < v ∧ (D.residue u, D.residue v) ∉ K.Xset) ∧
        ¬ (D.strictAt v ∧ u = D.boundary v) := by
  rw [RD, Finset.mem_sdiff, D.mem_normal_pairs_iff]
  constructor
  · rintro ⟨⟨u, v, rfl, rfl, h1, h2, h3⟩, hx⟩
    exact ⟨u, v, rfl, rfl, ⟨h1, h2, hx⟩, h3⟩
  · rintro ⟨u, v, rfl, rfl, ⟨h1, h2, hx⟩, h3⟩
    exact ⟨⟨u, v, rfl, rfl, h1, h2, h3⟩, hx⟩

theorem mem_RQ_iff (a b : Fin n) : (a, b) ∈ K.RQ ↔
    ∃ u v : ℤ, D.residue u = a ∧ D.residue v = b ∧
      (K.target.boundary v ≤ u ∧ u < v ∧ (D.residue u, D.residue v) ∉ K.XQset) ∧
        ¬ (K.target.strictAt v ∧ u = K.target.boundary v) := by
  rw [RQ, Finset.mem_sdiff, K.target.mem_normal_pairs_iff, K.target_residue]
  constructor
  · rintro ⟨⟨u, v, rfl, rfl, h1, h2, h3⟩, hx⟩
    exact ⟨u, v, rfl, rfl, ⟨h1, h2, hx⟩, h3⟩
  · rintro ⟨u, v, rfl, rfl, ⟨h1, h2, hx⟩, h3⟩
    exact ⟨⟨u, v, rfl, rfl, h1, h2, h3⟩, hx⟩

theorem RQ_eq : K.RQ = K.RD.map K.π2 := by
  ext ⟨a', b'⟩
  rw [K.mem_RQ_iff, Finset.mem_map]
  constructor
  · rintro ⟨u', v', rfl, rfl, h1, h2⟩
    refine ⟨(D.residue (K.σ u'), D.residue (K.σ v')), ?_, ?_⟩
    · rw [K.mem_RD_iff]
      refine ⟨K.σ u', K.σ v', rfl, rfl, ?_, ?_⟩
      · rw [K.exterior_lift_conjugacy, K.σ_σ, K.σ_σ]; exact h1
      · rw [K.strict_lift_conjugacy, K.σ_σ, K.σ_σ]; exact h2
    · rw [K.π2_res, K.σ_σ, K.σ_σ]
  · rintro ⟨⟨a, b⟩, hab, heq⟩
    obtain ⟨u, v, rfl, rfl, h1, h2⟩ := (K.mem_RD_iff a b).mp hab
    rw [K.π2_res] at heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨K.σ u, K.σ v, rfl, rfl, (K.exterior_lift_conjugacy u v).mp h1,
      fun h => h2 ((K.strict_lift_conjugacy u v).mpr h)⟩

end AliasContacts

end VerticalStripLLT.Circular
