import VerticalStripLLT.Circular.ChainSingletonOrientations
import VerticalStripLLT.Circular.ChainSingletonSubsets
import VerticalStripLLT.Circular.ChainSingletonInsertion

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace VerticalStripLLT.Circular.ChainSingletonData

open ChainSingletonSubsets

variable {n k : ℕ} {D : Diagram n} (S : ChainSingletonData D k)

/-- Normal edges between two chain vertices. -/
noncomputable def internalEdges : Finset (Edge D.area) :=
  D.edgeData.normalEdges.filter (fun e => e.tail ≠ S.isolated ∧ e.head ≠ S.isolated)

theorem normal_sdiff_internal :
    D.edgeData.normalEdges \ S.internalEdges = S.outEdges ∪ S.inEdges := by
  ext e
  simp only [internalEdges, outEdges, inEdges, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_union]
  have hne := e.tail_ne_head
  constructor
  · rintro ⟨he, hn⟩
    by_cases ht : e.tail = S.isolated
    · exact Or.inr ⟨he, ht⟩
    · by_cases hh : e.head = S.isolated
      · exact Or.inl ⟨he, hh⟩
      · exact absurd ⟨he, ht, hh⟩ hn
  · rintro (⟨he, hh⟩ | ⟨he, ht⟩)
    · exact ⟨he, fun h => h.2.2 hh⟩
    · exact ⟨he, fun h => h.2.1 ht⟩

theorem card_internal_forward :
    (S.internalEdges.filter (fun e => S.chainIdx e.tail < S.chainIdx e.head)).card =
      S.internalForwardCount := by
  unfold internalForwardCount
  rw [← Fintype.sum_prod_type' (f := fun i j =>
    if (S.chain i, S.chain j) ∈ D.pairGraph.normalEdges ∧ i < j then 1 else 0),
    Finset.sum_boole, Nat.cast_id]
  apply Finset.card_bij (fun e _ => (S.chainIdx e.tail, S.chainIdx e.head))
  · intro e he
    simp only [internalEdges, Finset.mem_filter] at he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, he.2⟩
    rw [S.chain_chainIdx _ he.1.2.1, S.chain_chainIdx _ he.1.2.2]
    exact (D.mem_pairGraph_normal_iff _).mpr ⟨e, he.1.1, rfl⟩
  · intro e he e' he' h
    simp only [internalEdges, Finset.mem_filter] at he he'
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    apply D.edge_eq_of_endpoints
    · rw [← S.chain_chainIdx _ he.1.2.1, ← S.chain_chainIdx _ he'.1.2.1, h1]
    · rw [← S.chain_chainIdx _ he.1.2.2, ← S.chain_chainIdx _ he'.1.2.2, h2]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨e, he, hep⟩ := (D.mem_pairGraph_normal_iff _).mp hp.1
    obtain ⟨ht, hh⟩ := Prod.mk.inj hep
    refine ⟨e, ?_, ?_⟩
    · simp only [internalEdges, Finset.mem_filter]
      rw [ht, hh, chainIdx_chain, chainIdx_chain]
      exact ⟨⟨he, S.chain_ne_isolated _, S.chain_ne_isolated _⟩, hp.2⟩
    · rw [ht, hh, chainIdx_chain, chainIdx_chain]

/-- Internal normal edges are forced or cyclic; only external edges remain. -/
theorem eval_expansion_reduce (m : ℕ) :
    evalElementary m (shiftedOrientationExpansion D) =
      (1 + MvPolynomial.C Polynomial.X) ^ S.internalForwardCount *
        ∑ A ∈ (S.outEdges ∪ S.inEdges).powerset,
          (MvPolynomial.C Polynomial.X : XPoly m) ^ A.card * evalElementary m (D.orientMono A) := by
  rw [D.shiftedOrientationExpansion_eq_sum, map_sum]
  simp only [map_mul, evalElementary_C, map_pow]
  rw [powerset_reduce D.edgeData.normalEdges S.internalEdges (Finset.filter_subset _ _)
    (fun A => evalElementary m (D.orientMono A)) _
    (fun e => S.chainIdx e.tail < S.chainIdx e.head)]
  · rw [S.normal_sdiff_internal]
    congr 2
    convert S.card_internal_forward using 2
    ext e
    simp
  · intro e he hP A hA
    simp only [internalEdges, Finset.mem_filter] at he
    have hpath : Relation.TransGen (D.edgeData.selected ∅) e.tail e.head := by
      have := S.chain_transGen hP
      rwa [S.chain_chainIdx _ he.2.1, S.chain_chainIdx _ he.2.2] at this
    show evalElementary m (D.orientMono (insert e A)) = evalElementary m (D.orientMono A)
    rw [D.orientMono_insert_of_strict_path e he.1 hpath A hA]
  · intro e he hP A _
    simp only [internalEdges, Finset.mem_filter] at he
    have hne : S.chainIdx e.head ≠ S.chainIdx e.tail := by
      intro h
      apply e.tail_ne_head
      rw [← S.chain_chainIdx _ he.2.1, ← S.chain_chainIdx _ he.2.2, h]
    have hlt : S.chainIdx e.head < S.chainIdx e.tail := lt_of_le_of_ne (not_lt.mp hP) hne
    have hpath : Relation.TransGen (D.edgeData.selected ∅) e.head e.tail := by
      have := S.chain_transGen hlt
      rwa [S.chain_chainIdx _ he.2.1, S.chain_chainIdx _ he.2.2] at this
    show evalElementary m (D.orientMono (insert e A)) = 0
    rw [D.orientMono_insert_of_reverse_strict_path e hpath A, map_zero]

theorem image_outEdges :
    S.outEdges.image (fun e => S.chainIdx e.tail) = Finset.univ.filter S.outgoing := by
  ext j
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, outgoing]
  constructor
  · rintro ⟨e, he, rfl⟩
    have heo := he
    simp only [outEdges, Finset.mem_filter] at he
    rw [S.chain_chainIdx _ (S.outEdges_tail heo)]
    exact (D.mem_pairGraph_normal_iff _).mpr ⟨e, he.1, by rw [he.2]⟩
  · intro h
    obtain ⟨e, he, hep⟩ := (D.mem_pairGraph_normal_iff _).mp h
    obtain ⟨ht, hh⟩ := Prod.mk.inj hep
    refine ⟨e, ?_, ?_⟩
    · simp only [outEdges, Finset.mem_filter]
      exact ⟨he, hh⟩
    · rw [ht, chainIdx_chain]

theorem image_inEdges :
    S.inEdges.image (fun e => S.chainIdx e.head) = Finset.univ.filter S.incoming := by
  ext j
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, incoming]
  constructor
  · rintro ⟨e, he, rfl⟩
    have hei := he
    simp only [inEdges, Finset.mem_filter] at he
    rw [S.chain_chainIdx _ (S.inEdges_head hei)]
    exact (D.mem_pairGraph_normal_iff _).mpr ⟨e, he.1, by rw [he.2]⟩
  · intro h
    obtain ⟨e, he, hep⟩ := (D.mem_pairGraph_normal_iff _).mp h
    obtain ⟨ht, hh⟩ := Prod.mk.inj hep
    refine ⟨e, ?_, ?_⟩
    · simp only [inEdges, Finset.mem_filter]
      exact ⟨he, ht⟩
    · rw [hh, chainIdx_chain]

theorem injOn_outEdges : Set.InjOn (fun e : Edge D.area => S.chainIdx e.tail) S.outEdges := by
  intro e he e' he' h
  have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
  have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp he')).2
  apply D.edge_eq_of_endpoints
  · rw [← S.chain_chainIdx _ (S.outEdges_tail (Finset.mem_coe.mp he)),
      ← S.chain_chainIdx _ (S.outEdges_tail (Finset.mem_coe.mp he'))]
    exact congrArg S.chain h
  · rw [h1, h2]

theorem injOn_inEdges : Set.InjOn (fun e : Edge D.area => S.chainIdx e.head) S.inEdges := by
  intro e he e' he' h
  have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
  have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp he')).2
  apply D.edge_eq_of_endpoints
  · rw [h1, h2]
  · rw [← S.chain_chainIdx _ (S.inEdges_head (Finset.mem_coe.mp he)),
      ← S.chain_chainIdx _ (S.inEdges_head (Finset.mem_coe.mp he'))]
    exact congrArg S.chain h

theorem card_outgoing_erase_last :
    ((Finset.univ.filter S.outgoing).erase (Fin.last k)).card =
      ∑ i : Fin k, if S.outgoing i.castSucc then 1 else 0 := by
  have h : (Finset.univ.filter S.outgoing).erase (Fin.last k) =
      Finset.univ.filter (fun j => S.outgoing j ∧ j ≠ Fin.last k) := by
    ext j
    simp [and_comm]
  rw [h, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [ne_eq, not_true_eq_false, and_false, ite_false, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply if_congr _ rfl rfl
  simp [Fin.castSucc_ne_last]

theorem sum_gapEps (m : ℕ) :
    (∑ j : Fin (k + 2), if S.gapEps j then (MvPolynomial.C Polynomial.X : XPoly m) else 0) =
      (((if S.incoming 0 then 1 else 0) + (∑ i : Fin k, if S.outgoing i.castSucc then 1 else 0) +
        (if S.outgoing (Fin.last k) then 1 else 0) : ℕ) : XPoly m) *
          MvPolynomial.C Polynomial.X := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have h0 : S.gapEps 0 ↔ S.incoming 0 := by simp [gapEps]
  have hl : S.gapEps (Fin.last k).succ ↔ S.outgoing (Fin.last k) := by
    simp only [gapEps, Fin.val_succ, Fin.val_last, Nat.add_sub_cancel]
    rw [ite_eq_right (by lia)]
    rfl
  have hi : ∀ i : Fin k, S.gapEps i.castSucc.succ ↔ S.outgoing i.castSucc := by
    intro i
    simp only [gapEps, Fin.val_succ, Fin.val_castSucc, Nat.add_sub_cancel]
    rw [ite_eq_right (by lia)]
    rfl
  have hconv : ∀ (P : Prop) [Decidable P], (if P then (MvPolynomial.C Polynomial.X : XPoly m)
      else 0) = ((if P then 1 else 0 : ℕ) : XPoly m) * MvPolynomial.C Polynomial.X := by
    intro P _
    split_ifs <;> simp
  simp only [h0, hl, hi, hconv]
  push_cast
  simp only [add_mul, Finset.sum_mul]
  ring

end VerticalStripLLT.Circular.ChainSingletonData
