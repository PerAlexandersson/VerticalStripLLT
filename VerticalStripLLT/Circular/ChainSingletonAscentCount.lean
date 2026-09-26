import VerticalStripLLT.Circular.ChainSingletonColorings
import VerticalStripLLT.Circular.ChainSingletonAscents
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Decomposition of the actual diagram ascent count into internal and cross incidences. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace PairGraph

theorem ascentCount_eq_sum {n m : ℕ} (G : PairGraph n) (c : Fin n → Fin m) :
    G.ascentCount c = ∑ u : Fin n, ∑ v : Fin n,
      if (u, v) ∈ G.normalEdges ∧ c u < c v then 1 else 0 := by
  calc
    _ = ∑ e : Fin n × Fin n,
        if e ∈ G.normalEdges ∧ c e.1 < c e.2 then 1 else 0 := by
      rw [Finset.sum_boole]
      unfold ascentCount
      congr 1
      ext e
      simp
    _ = _ := by rw [Fintype.sum_prod_type]

end PairGraph

namespace ChainSingletonData

variable {n k : ℕ} {D : Diagram n} (S : ChainSingletonData D k)

noncomputable def internalForwardCount : ℕ :=
  ∑ i : Fin (k + 1), ∑ j : Fin (k + 1),
    if (S.chain i, S.chain j) ∈ D.pairGraph.normalEdges ∧ i < j then 1 else 0

def outgoing (i : Fin (k + 1)) : Prop :=
  (S.chain i, S.isolated) ∈ D.pairGraph.normalEdges

def incoming (i : Fin (k + 1)) : Prop :=
  (S.isolated, S.chain i) ∈ D.pairGraph.normalEdges

theorem incoming_succ_iff (i : Fin k) : S.incoming i.succ ↔ S.outgoing i.castSucc :=
  (S.normal_across_succ i).symm

/-- Strictly increasing chain colors make every internal normal comparison fixed. -/
theorem ascentCount_eq_internal_add_cross {m : ℕ} (c : Fin n → Fin m)
    (hc : StrictMono (fun i => c (S.chain i))) :
    (D.edgeData.ascentEdges c).card = S.internalForwardCount +
      ∑ i : Fin (k + 1),
        ((if S.outgoing i ∧ c (S.chain i) < c S.isolated then 1 else 0) +
          (if S.incoming i ∧ c S.isolated < c (S.chain i) then 1 else 0)) := by
  rw [← D.pairGraph_ascentCount, PairGraph.ascentCount_eq_sum]
  have hreindex : (∑ u : Fin n, ∑ v : Fin n,
      if (u, v) ∈ D.pairGraph.normalEdges ∧ c u < c v then 1 else 0) =
      ∑ u : Fin (k + 1) ⊕ Unit, ∑ v : Fin (k + 1) ⊕ Unit,
        if (S.vertices u, S.vertices v) ∈ D.pairGraph.normalEdges ∧
          c (S.vertices u) < c (S.vertices v) then 1 else 0 := by
    symm
    refine Fintype.sum_equiv S.vertices _ _ ?_
    intro u
    exact S.vertices.sum_comp (fun v =>
      if (S.vertices u, v) ∈ D.pairGraph.normalEdges ∧ c (S.vertices u) < c v
        then 1 else 0)
  rw [hreindex]
  simp_rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, lt_self_iff_false,
    and_false, ite_false, add_zero]
  change StrictMono (fun i => c (S.vertices (.inl i))) at hc
  simp_rw [hc.lt_iff_lt]
  simp only [internalForwardCount, outgoing, incoming, chain, isolated,
    Finset.sum_add_distrib]
  ac_rfl

noncomputable def baseAscentCount : ℕ :=
  S.internalForwardCount + ∑ i : Fin k, if S.outgoing i.castSucc then 1 else 0

/-- The remaining ascents are exactly the occupied insertion gaps. -/
theorem ascentCount_eq_base_add_gaps {m : ℕ} (c : Fin n → Fin m)
    (hc : StrictMono (fun i => c (S.chain i))) :
    (D.edgeData.ascentEdges c).card = S.baseAscentCount +
      (if S.incoming 0 ∧ c S.isolated < c (S.chain 0) then 1 else 0) +
      (if S.outgoing (Fin.last k) ∧ c (S.chain (Fin.last k)) < c S.isolated
        then 1 else 0) +
      ∑ i : Fin k,
        if S.outgoing i.castSucc ∧ c (S.chain i.castSucc) < c S.isolated ∧
          c S.isolated < c (S.chain i.succ) then 1 else 0 := by
  rw [S.ascentCount_eq_internal_add_cross c hc,
    chain_singleton_ascents _ hc _ S.outgoing S.incoming S.incoming_succ_iff]
  unfold baseAscentCount
  ac_rfl

end ChainSingletonData

end VerticalStripLLT.Circular
