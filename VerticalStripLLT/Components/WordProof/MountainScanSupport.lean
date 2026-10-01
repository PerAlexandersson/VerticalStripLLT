import VerticalStripLLT.Components.WordProof.MountainScan
import VerticalStripLLT.Components.WordProof.BlockWordSupport

/-! Support-sensitive continuation lemmas for the literal mountain scan. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {K : Type*} [CommRing K]

private theorem mountain_block_support_lt_succ {n k : ℕ} (hk : k < n)
    (B T : Finset (Fin n))
    (hB : B ⊆ Finset.univ.filter (fun v : Fin n => v.val < k))
    (hT : T ⊆ B) :
    ∀ v ∈ blockWord (insert ⟨k, hk⟩ B) T, v.val < k + 1 := by
  intro v hv
  have hvB : v ∈ insert ⟨k, hk⟩ B :=
    (mem_blockWord_iff (insert ⟨k, hk⟩ B) T
      (hT.trans (Finset.subset_insert _ _)) v).mp hv
  rcases Finset.mem_insert.mp hvB with rfl | hvB
  · exact Nat.lt_succ_self k
  · exact Nat.lt_succ_of_lt (Finset.mem_filter.mp (hB hvB)).2

theorem mountainScan_congr_below (a : ℕ → K) (n k : ℕ)
    {f g : List (Fin n) → K}
    (hfg : ∀ w, (∀ v ∈ w, v.val < k) → f w = g w) :
    mountainScan a n k f = mountainScan a n k g := by
  induction k generalizing f g with
  | zero => exact hfg [] (by simp)
  | succ k ih =>
      simp only [mountainScan]
      have hlow : ∀ w, (∀ v ∈ w, v.val < k) → f w = g w := by
        intro w hw
        apply hfg w
        intro v hv
        exact Nat.lt_trans (hw v hv) (Nat.lt_succ_self k)
      split_ifs with hk
      · rw [ih hlow]
        congr 1
        apply Finset.sum_congr rfl
        intro B hB
        apply Finset.sum_congr rfl
        intro T hT
        congr 1
        apply ih
        intro w hw
        apply hfg
        intro v hv
        rcases List.mem_append.mp hv with hvblock | hvtail
        · exact mountain_block_support_lt_succ hk B T
            (Finset.mem_powerset.mp hB) (Finset.mem_powerset.mp hT) v hvblock
        · exact Nat.lt_succ_of_lt (hw v hvtail)
      · rw [ih hlow]

theorem mountainScan_eq_zero_of_zero_below (a : ℕ → K) (n k : ℕ)
    (f : List (Fin n) → K)
    (hzero : ∀ w, (∀ v ∈ w, v.val < k) → f w = 0) :
    mountainScan a n k f = 0 := by
  rw [mountainScan_congr_below a n k (f := f) (g := fun _ => 0) hzero]
  exact mountainScan_zero_continuation a n k

end

end VerticalStripLLT.Components
