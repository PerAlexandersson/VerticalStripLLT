import VerticalStripLLT.Circular.ReachableMaximum
import Mathlib.Tactic.Linarith

/-! Translation equivariance for bounded integer reachability. -/

namespace VerticalStripLLT.Circular

/-- Translation-equivariance of a relation gives translation-equivariance of its
reflexive transitive closure. -/
theorem reflTransGen_translate_iff (S : ℤ → ℤ → Prop) (t z w : ℤ)
    (hS : ∀ x y, S (x + t) (y + t) ↔ S x y) :
    Relation.ReflTransGen S (z + t) (w + t) ↔ Relation.ReflTransGen S z w := by
  constructor
  · intro h
    have hsub := Relation.ReflTransGen.lift (fun x : ℤ => x - t)
      (fun x y hxy => (hS (x - t) (y - t)).mp (by simpa using hxy)) _ _ h
    simpa [Function.onFun] using hsub
  · intro h
    exact Relation.ReflTransGen.lift (fun x : ℤ => x + t)
      (fun x y hxy => (hS x y).mpr hxy) _ _ h

/-- The maximum of bounded reachable vertices commutes with relation translations. -/
theorem reachableMaximum_translate (S : ℤ → ℤ → Prop) (B : ℕ) (t z : ℤ)
    (hS : ∀ x y, S (x + t) (y + t) ↔ S x y) :
    reachableMaximum S B (z + t) = reachableMaximum S B z + t := by
  apply le_antisymm
  · have hreach : Relation.ReflTransGen S z (reachableMaximum S B (z + t) - t) := by
      apply (reflTransGen_translate_iff S t z (reachableMaximum S B (z + t) - t) hS).mp
      simpa using maximum_reachable S B (z + t)
    have hmem : reachableMaximum S B (z + t) - t ∈ reachableVertices S B z := by
      apply (mem_reachableVertices_iff S B z _).mpr
      have hbounds := (mem_reachableVertices_iff S B (z + t)
        (reachableMaximum S B (z + t))).mp
        (maximum_mem_reachableVertices S B (z + t))
      exact ⟨by linarith, by linarith, hreach⟩
    have hle := Finset.le_max' _ _ hmem
    change reachableMaximum S B (z + t) - t ≤ reachableMaximum S B z at hle
    linarith
  · have hreach : Relation.ReflTransGen S (z + t) (reachableMaximum S B z + t) :=
      (reflTransGen_translate_iff S t z (reachableMaximum S B z) hS).mpr
        (maximum_reachable S B z)
    have hmem : reachableMaximum S B z + t ∈ reachableVertices S B (z + t) := by
      apply (mem_reachableVertices_iff S B (z + t) _).mpr
      have hbounds := (mem_reachableVertices_iff S B z (reachableMaximum S B z)).mp
        (maximum_mem_reachableVertices S B z)
      exact ⟨by linarith, by linarith, hreach⟩
    exact Finset.le_max' _ _ hmem

end VerticalStripLLT.Circular
