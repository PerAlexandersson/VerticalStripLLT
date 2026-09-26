import VerticalStripLLT.SecondBounceSpec
-- Local helper module: VerticalStripLLT.SecondBounceAssembly

/-! ## Assembly of the second bounce identity -/

namespace VerticalStripLLT
namespace BounceHRV

open scoped BigOperators

variable {n : ℕ}

/-- The abstract second-bounce identity: the orientation expansions of the source and the
successor agree, given the graph data relating both to the common background `B`. -/
theorem orientationExpansionAt_secondBounce_core {B P T : SchroderPath n} {a i y t : Fin n}
    (hy : y.val = i.val + 1) (hyt : y < t) (hai : a < i) (hiy : (i, y) ∈ B.normalEdges)
    (hSinv : B.strictEdges.map (swapVertexPair i y) = B.strictEdges)
    (hNinv : (B.normalEdges.erase (i, y)).map (swapVertexPair i y) =
      B.normalEdges.erase (i, y))
    (hfreshP : (y, t) ∉ B.normalEdges)
    (hPN : P.normalEdges = insert (y, t) B.normalEdges)
    (hPS : P.strictEdges = insert (a, i) (insert (i, t) B.strictEdges))
    (hfreshT : (a, i) ∉ B.normalEdges)
    (hTN : T.normalEdges = insert (a, i) B.normalEdges)
    (hTS : T.strictEdges = insert (a, y) (insert (y, t) B.strictEdges)) (z : Q) :
    orientationExpansionAt P z = orientationExpansionAt T z := by
  classical
  have hP : orientationExpansionAt P z = ∑ p : Bool × Orientation B,
      MvPolynomial.C (z ^ (orientationAsc B p.2 + if p.1 then 1 else 0)) *
        fiberMono (gh (RP2 a i y t p.1 p.2)) := by
    unfold orientationExpansionAt
    rw [← Equiv.sum_comp (orientationInsertEquiv (y, t) hfreshP hPN).symm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [orientationAsc_insert, hrvMonomial_eq_fiberMono, hrv_eq_gh,
      gh_congr (upwardStep_secondSource_iff hfreshP hPN hPS p.1 p.2)]
  have hT : orientationExpansionAt T z = ∑ q : Bool × Orientation B,
      MvPolynomial.C (z ^ (orientationAsc B q.2 + if q.1 then 1 else 0)) *
        fiberMono (gh (RT2 a i y t q.1 q.2)) := by
    unfold orientationExpansionAt
    rw [← Equiv.sum_comp (orientationInsertEquiv (a, i) hfreshT hTN).symm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [orientationAsc_insert, hrvMonomial_eq_fiberMono, hrv_eq_gh,
      gh_congr (upwardStep_secondSucc_iff hfreshT hTN hTS q.1 q.2)]
  rw [hP, hT]
  symm
  rw [← (secondMatch_bijective hy hyt hiy hSinv hNinv).sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨hasc, hmono⟩ := secondMatch_spec hy hyt hai hiy hSinv hNinv p
  rw [← hasc, hmono]

end BounceHRV
end VerticalStripLLT

namespace VerticalStripLLT
