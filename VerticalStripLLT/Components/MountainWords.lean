import VerticalStripLLT.Components.BlockCancellation

/-! Maximum insertion for the increasing side of a mountain word. -/

namespace VerticalStripLLT.Components

open scoped BigOperators
open Classical

noncomputable section

variable {V : Type*} [LinearOrder V]

/-- Appending a strict maximum to a finite set appends it to its increasing word. -/
theorem incWord_insert_max (B : Finset V) (r : V)
    (hr : ∀ v ∈ B, v < r) :
    incWord (insert r B) = incWord B ++ [r] := by
  have hrB : r ∉ B := by
    intro hB
    exact (lt_irrefl r) (hr r hB)
  let L := incWord B ++ [r]
  have hLset : L.toFinset = insert r B := by
    ext v
    simp [L, incWord]
  have hLnodup : L.Nodup := by
    change (incWord B ++ [r]).Nodup
    rw [← List.concat_eq_append]
    have hsort : (incWord B).Nodup := by
      simpa [incWord] using B.sort_nodup (· ≤ ·)
    apply hsort.concat
    simpa [incWord] using hrB
  have hLpair : L.Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨Finset.pairwise_sort B (· ≤ ·), by simp, ?_⟩
    intro v hv w hw
    have hw' : w = r := by simpa using hw
    subst w
    exact (hr v (by simpa [incWord] using hv)).le
  have hsort := (List.toFinset_sort (r := (· ≤ ·)) hLnodup).2 hLpair
  rw [hLset] at hsort
  exact hsort

/-- A mountain with peak `r` is a block word when `r` is above the block. -/
theorem blockWord_insert_max (B T : Finset V) (r : V)
    (hT : T ⊆ B) (hr : ∀ v ∈ B, v < r) :
    blockWord (insert r B) T =
      incWord (B \ T) ++ [r] ++ decWord T := by
  have hrB : r ∉ B := by
    intro hB
    exact (lt_irrefl r) (hr r hB)
  have hrT : r ∉ T := fun h => hrB (hT h)
  have hdiff : insert r B \ T = insert r (B \ T) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    grind
  rw [blockWord, hdiff, incWord_insert_max (B \ T) r
    (fun v hv => hr v (Finset.mem_sdiff.mp hv).1)]

/-- Block cancellation written in the increasing/decreasing mountain notation. -/
theorem blockCancellation_insert_max (R : V → V → Prop)
    (hinc : ∀ ⦃u v⦄, R u v → u < v) (B : Finset V) (r : V)
    (hr : ∀ v ∈ B, v < r) :
    (∑ T ∈ B.powerset,
      (-1 : ℤ) ^ T.card *
        (if wordCompatible R (incWord (B \ T) ++ [r] ++ decWord T)
          then 1 else 0)) =
      if (∀ u ∈ B, ¬sinkOn R (insert r B) u) then 1 else 0 := by
  calc
    (∑ T ∈ B.powerset,
        (-1 : ℤ) ^ T.card *
          (if wordCompatible R (incWord (B \ T) ++ [r] ++ decWord T)
            then 1 else 0)) =
        ∑ T ∈ B.powerset,
          (-1 : ℤ) ^ T.card *
            (if wordCompatible R (blockWord (insert r B) T)
              then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [blockWord_insert_max B T r (Finset.mem_powerset.mp hT) hr]
    _ = if (∀ u ∈ B, ¬sinkOn R (insert r B) u) then 1 else 0 :=
      blockCancellation R hinc (insert r B) B (Finset.subset_insert _ _)

end

end VerticalStripLLT.Components
