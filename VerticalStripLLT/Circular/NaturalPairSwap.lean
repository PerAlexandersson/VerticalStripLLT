import VerticalStripLLT.Circular.PeriodicBoundarySwap
import VerticalStripLLT.Circular.PeriodicSwapResidue
import VerticalStripLLT.Circular.BoundaryEdges
import VerticalStripLLT.Circular.PairColoringBridge
import VerticalStripLLT.SwapSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Periodic adjacent swaps preserve the non-bridge natural endpoint pairs. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular

open scoped Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

noncomputable def naturalPairs : Finset (Fin n × Fin n) :=
  Finset.univ.map D.endpointEmbedding

theorem mem_naturalPairs_iff (x : Fin n × Fin n) :
    x ∈ D.naturalPairs ↔ ∃ e : Edge D.area, (e.tail, e.head) = x := by
  simp [naturalPairs, endpointEmbedding]

private theorem residue_head_of_tail_length (e : Edge D.area) :
    D.residue ((e.tail.val : ℤ) + (e.length.val : ℤ)) = e.head := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [D.residue_coe_val]
  have hnat := e.tail_add_length_mod
  exact_mod_cast hnat

private theorem boundaryNaturalLift_of_edge_instance (e : Edge D.area) :
    D.boundaryNaturalLift (e.tail.val : ℤ)
      ((e.tail.val : ℤ) + (e.length.val : ℤ)) := by
  apply D.boundaryNaturalLift_of_edge (e := e)
  · exact (D.residue_head_of_tail_length e).symm
  · ring

private theorem periodicBridge_of_natural_endpoints (hn : 2 ≤ n)
    {u v p : ℤ} (h : D.boundaryNaturalLift u v)
    (hu : D.residue u = D.residue p)
    (hv : D.residue v = D.residue (p + 1)) : periodicBridge n p u v := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, u = p + n * k := by
    refine ⟨(u - p) / n, ?_⟩
    have hm := (D.residue_eq_iff_mod_sub_zero).mp hu
    have hd := Int.mul_ediv_add_emod (u - p) n
    rw [hm] at hd
    linarith
  obtain ⟨l, hl⟩ : ∃ l : ℤ, v = p + 1 + n * l := by
    refine ⟨(v - (p + 1)) / n, ?_⟩
    have hm := (D.residue_eq_iff_mod_sub_zero).mp hv
    have hd := Int.mul_ediv_add_emod (v - (p + 1)) n
    rw [hm] at hd
    linarith
  have hpos := D.boundaryNaturalLift_length_pos h
  have hlt := D.boundaryNaturalLift_length_lt h
  refine ⟨k, hk, ?_⟩
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have : l = k := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt' | hgt'
    · have : l + 1 ≤ k := by lia
      nlinarith
    · have : k + 1 ≤ l := by lia
      nlinarith
  simpa [this] using hl

private theorem naturalPairs_erase_swap_mem (hn : 2 ≤ n) (p : ℤ)
    (hsame : D.boundary (p + 1) = D.boundary p)
    (havoid : ∀ z k : ℤ, D.boundary z ≠ p + 1 + n * k) :
    ∀ ⦃x : Fin n × Fin n⦄, x ∈ D.naturalPairs.erase
      (D.residue p, D.residue (p + 1)) →
      swapVertexPair (D.residue p) (D.residue (p + 1)) x ∈
        D.naturalPairs.erase (D.residue p, D.residue (p + 1)) := by
  classical
  intro x hx
  rcases Finset.mem_erase.mp hx with ⟨hxne, hxmem⟩
  rcases (D.mem_naturalPairs_iff _).mp hxmem with ⟨e, he⟩
  let u : ℤ := e.tail.val
  let v : ℤ := u + e.length.val
  have hnat : D.boundaryNaturalLift u v := D.boundaryNaturalLift_of_edge_instance e
  have hhead : D.residue v = e.head := D.residue_head_of_tail_length e
  have htail : D.residue u = e.tail := Orientation.residue_intCast_eq e.tail
  have hnot : ¬ periodicBridge n p u v := by
    rintro ⟨k, hu, hv⟩
    apply hxne
    rw [← he, ← htail, ← hhead, hu, hv, D.residue_add_period,
      D.residue_add_period]
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have hrel := (periodicSwap_boundary_relation n p hn' D.boundary
    D.boundary_add_period hsame havoid u v).mp ⟨hnat.1, hnat.2, hnot⟩
  have hnew : D.boundaryNaturalLift (periodicSwap n p u) (periodicSwap n p v) :=
    ⟨hrel.1, hrel.2.1⟩
  let e' := D.edgeFromLift (periodicSwap n p u) (periodicSwap n p v) hnew
  have hpair : (e'.tail, e'.head) =
      swapVertexPair (D.residue p) (D.residue (p + 1)) (e.tail, e.head) := by
    change ((D.edgeFromLift _ _ hnew).tail, (D.edgeFromLift _ _ hnew).head) = _
    rw [D.edgeFromLift_tail, D.edgeFromLift_head, swapVertexPair_apply,
      D.residue_periodicSwap hn p u, D.residue_periodicSwap hn p v, htail, hhead]
  rw [← he]
  refine Finset.mem_erase.mpr ⟨?_, (D.mem_naturalPairs_iff _).mpr ⟨e', hpair⟩⟩
  intro hbridge
  have hpairs := hpair.trans hbridge
  have hu : D.residue (periodicSwap n p u) = D.residue p := by
    have hh := congrArg Prod.fst hpairs
    change (D.edgeFromLift _ _ hnew).tail = _ at hh
    rwa [D.edgeFromLift_tail] at hh
  have hv : D.residue (periodicSwap n p v) = D.residue (p + 1) := by
    have hh := congrArg Prod.snd hpairs
    exact hh
  exact hrel.2.2 (D.periodicBridge_of_natural_endpoints hn hnew hu hv)

theorem naturalPairs_erase_map_swap (hn : 2 ≤ n) (p : ℤ)
    (hsame : D.boundary (p + 1) = D.boundary p)
    (havoid : ∀ z k : ℤ, D.boundary z ≠ p + 1 + n * k) :
    (D.naturalPairs.erase (D.residue p, D.residue (p + 1))).map
        (swapVertexPair (D.residue p) (D.residue (p + 1))) =
      D.naturalPairs.erase (D.residue p, D.residue (p + 1)) := by
  classical
  let σ := swapVertexPair (D.residue p) (D.residue (p + 1))
  have hσ : Function.Involutive σ := by
    intro x
    ext <;> simp [σ, swapVertexPair_apply]
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact D.naturalPairs_erase_swap_mem hn p hsame havoid hy
  · intro hx
    have hy := D.naturalPairs_erase_swap_mem hn p hsame havoid hx
    refine Finset.mem_map.mpr ⟨σ x, hy, ?_⟩
    exact hσ x

theorem normalPairs_eq_sdiff :
    D.pairGraph.normalEdges = D.naturalPairs \ D.pairGraph.strictEdges := by
  change (Finset.univ \ D.strict).map D.endpointEmbedding =
    Finset.univ.map D.endpointEmbedding \ D.strict.map D.endpointEmbedding
  rw [Finset.map_sdiff]

end Diagram
end VerticalStripLLT.Circular
