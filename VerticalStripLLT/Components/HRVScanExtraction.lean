import VerticalStripLLT.Components.MountainScanSupport
import VerticalStripLLT.Components.HRVBlockContinuation

/-!
# Per-orientation mountain scan extraction

For a fixed forward orientation, the literal mountain scan of the actual
full-support compatibility indicator at HRV cutoff `k` equals the product of the
elementary coefficients of the actual HRV fibers rooted below `k`.  The proof is
an induction on the cutoff.  At the next rank, signed first-block cancellation
leaves the next actual fiber as the only surviving peak block, while the skipped
term either vanishes (fixed root) or is the previous cutoff (no fiber).
-/

namespace VerticalStripLLT.Circular.Orientation

open Classical
open scoped BigOperators
open VerticalStripLLT.Components

variable {n : ℕ} {D : Diagram n} {K : Type*} [CommRing K]

/-- The actual per-state full-support compatibility continuation at an HRV cutoff. -/
noncomputable def hrvScanContinuation (θ : Orientation D) (k : ℕ) (w : List (Fin n)) : K :=
  if fullOn (θ.hrvInitialSupport k) w ∧ wordCompatible (D.edgeData.selected θ.val) w
    then 1 else 0

private theorem mk_notMem_filter_lt (k : ℕ) (hk : k < n) :
    (⟨k, hk⟩ : Fin n) ∉ Finset.univ.filter (fun v : Fin n => v.val < k) := by
  simp

private theorem filter_lt_succ_eq_insert (k : ℕ) (hk : k < n) :
    Finset.univ.filter (fun v : Fin n => v.val < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun v : Fin n => v.val < k)) := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  simp only [Fin.ext_iff]
  lia

private theorem prod_filter_lt_succ (a : ℕ → K) (θ : Orientation D) (k : ℕ) (hk : k < n) :
    (∏ r ∈ Finset.univ.filter (fun r : Fin n => r.val < k + 1),
        a ((Finset.univ.filter (fun v => θ.hrv v = r)).card)) =
      (∏ r ∈ Finset.univ.filter (fun r : Fin n => r.val < k),
        a ((Finset.univ.filter (fun v => θ.hrv v = r)).card)) *
        a ((Finset.univ.filter (fun v => θ.hrv v = ⟨k, hk⟩)).card) := by
  rw [filter_lt_succ_eq_insert k hk, Finset.prod_insert (mk_notMem_filter_lt k hk)]
  exact mul_comm _ _

/-- The literal scan recursion below the alphabet size. -/
private theorem mountainScan_succ_of_lt (a : ℕ → K) {k : ℕ} (hk : k < n)
    (f : List (Fin n) → K) :
    mountainScan a n (k + 1) f = mountainScan a n k f +
      ∑ B ∈ (Finset.univ.filter (fun v : Fin n => v.val < k)).powerset, ∑ T ∈ B.powerset,
        a (B.card + 1) * (-1 : K) ^ T.card *
          mountainScan a n k (fun w => f (blockWord (insert ⟨k, hk⟩ B) T ++ w)) := by
  simp only [mountainScan, dite_eq_left hk]

/-- Words below a fixed root cannot enumerate the support containing that root. -/
private theorem skip_term_eq_zero_of_root (a : ℕ → K) (θ : Orientation D) (k : ℕ)
    (hk : k < n) (hroot : θ.hrv ⟨k, hk⟩ = ⟨k, hk⟩) :
    mountainScan a n k (θ.hrvScanContinuation (k + 1)) = 0 := by
  apply mountainScan_eq_zero_of_zero_below
  intro w hw
  have hmem : (⟨k, hk⟩ : Fin n) ∈ θ.hrvInitialSupport (k + 1) := by
    rw [θ.mem_hrvInitialSupport, hroot]
    exact Nat.lt_succ_self k
  have hnot : ¬ fullOn (θ.hrvInitialSupport (k + 1)) w := by
    rintro ⟨_, hfull⟩
    exact lt_irrefl k (hw _ ((hfull ⟨k, hk⟩).mpr hmem))
  simp only [hrvScanContinuation]
  exact ite_eq_right (fun h => hnot h.1)

/-- One peak block at rank `k` survives only when it is the actual fiber of `k`. -/
private theorem peak_term (a : ℕ → K) (θ : Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) (k : ℕ) (hk : k < n)
    (B : Finset (Fin n)) (hB : B ⊆ Finset.univ.filter (fun v : Fin n => v.val < k)) :
    (∑ T ∈ B.powerset, a (B.card + 1) * (-1 : K) ^ T.card *
      mountainScan a n k (fun w =>
        θ.hrvScanContinuation (k + 1) (blockWord (insert ⟨k, hk⟩ B) T ++ w))) =
      if insert (⟨k, hk⟩ : Fin n) B = Finset.univ.filter (fun v => θ.hrv v = ⟨k, hk⟩) then
        a (B.card + 1) * mountainScan a n k (θ.hrvScanContinuation k)
      else 0 := by
  have hrB : (⟨k, hk⟩ : Fin n) ∉ B := fun h => mk_notMem_filter_lt k hk (hB h)
  have herase : (insert (⟨k, hk⟩ : Fin n) B).erase ⟨k, hk⟩ = B := Finset.erase_insert hrB
  have hr : (⟨k, hk⟩ : Fin n) ∈ insert ⟨k, hk⟩ B := Finset.mem_insert_self _ _
  have hmax : ∀ v ∈ insert (⟨k, hk⟩ : Fin n) B, v ≤ ⟨k, hk⟩ := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hvB
    · exact le_rfl
    · exact Fin.le_iff_val_le_val.mpr (le_of_lt (Finset.mem_filter.mp (hB hvB)).2)
  have hcancel : ∀ w : List (Fin n),
      (∑ T ∈ B.powerset, (-1 : K) ^ T.card *
        θ.hrvScanContinuation (k + 1) (blockWord (insert ⟨k, hk⟩ B) T ++ w)) =
        if insert (⟨k, hk⟩ : Fin n) B = Finset.univ.filter (fun v => θ.hrv v = ⟨k, hk⟩) then
          θ.hrvScanContinuation k w
        else 0 := by
    intro w
    have h := θ.signed_blockContinuation_hrvInitialSupport (K := K) hforward
      (insert ⟨k, hk⟩ B) ⟨k, hk⟩ hr hmax w
    rw [herase] at h
    exact h
  calc (∑ T ∈ B.powerset, a (B.card + 1) * (-1 : K) ^ T.card *
        mountainScan a n k (fun w =>
          θ.hrvScanContinuation (k + 1) (blockWord (insert ⟨k, hk⟩ B) T ++ w)))
      = ∑ T ∈ B.powerset, mountainScan a n k (fun w =>
          a (B.card + 1) * (-1 : K) ^ T.card *
            θ.hrvScanContinuation (k + 1) (blockWord (insert ⟨k, hk⟩ B) T ++ w)) := by
        apply Finset.sum_congr rfl
        intro T _
        exact (mountainScan_mul a n k _ _).symm
    _ = mountainScan a n k (fun w => ∑ T ∈ B.powerset,
          a (B.card + 1) * (-1 : K) ^ T.card *
            θ.hrvScanContinuation (k + 1) (blockWord (insert ⟨k, hk⟩ B) T ++ w)) :=
        (mountainScan_sum a n k B.powerset _).symm
    _ = mountainScan a n k (fun w => a (B.card + 1) *
          if insert (⟨k, hk⟩ : Fin n) B = Finset.univ.filter (fun v => θ.hrv v = ⟨k, hk⟩)
            then θ.hrvScanContinuation k w else 0) := by
        apply mountainScan_congr
        intro w
        rw [← hcancel w, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T _
        ring
    _ = a (B.card + 1) * mountainScan a n k (fun w =>
          if insert (⟨k, hk⟩ : Fin n) B = Finset.univ.filter (fun v => θ.hrv v = ⟨k, hk⟩)
            then θ.hrvScanContinuation k w else 0) :=
        mountainScan_mul a n k _ _
    _ = if insert (⟨k, hk⟩ : Fin n) B = Finset.univ.filter (fun v => θ.hrv v = ⟨k, hk⟩) then
          a (B.card + 1) * mountainScan a n k (θ.hrvScanContinuation k)
        else 0 := by
        by_cases hU : insert (⟨k, hk⟩ : Fin n) B =
            Finset.univ.filter (fun v => θ.hrv v = ⟨k, hk⟩)
        all_goals simp [hU, mountainScan_zero_continuation]

/-- The literal scan at HRV cutoff `k` is the product over the actual fibers rooted below `k`. -/
theorem mountainScan_hrvScanContinuation (θ : Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) (a : ℕ → K) (ha0 : a 0 = 1)
    (k : ℕ) (hk : k ≤ n) :
    mountainScan a n k (θ.hrvScanContinuation k) =
      ∏ r ∈ Finset.univ.filter (fun r : Fin n => r.val < k),
        a ((Finset.univ.filter (fun v => θ.hrv v = r)).card) := by
  induction k with
  | zero =>
      have hfilter : Finset.univ.filter (fun r : Fin n => r.val < 0) = ∅ :=
        Finset.filter_false_of_mem (fun r _ => Nat.not_lt_zero r.val)
      rw [hfilter, Finset.prod_empty, mountainScan_zero]
      simp only [hrvScanContinuation]
      exact ite_eq_left ⟨(fullOn_nil _).mpr θ.hrvInitialSupport_zero, List.Pairwise.nil⟩
  | succ k ih =>
      have hklt : k < n := Nat.lt_of_succ_le hk
      have hprev := ih (Nat.le_of_lt hklt)
      have hpeak : (∑ B ∈ (Finset.univ.filter (fun v : Fin n => v.val < k)).powerset,
          ∑ T ∈ B.powerset, a (B.card + 1) * (-1 : K) ^ T.card *
            mountainScan a n k (fun w =>
              θ.hrvScanContinuation (k + 1) (blockWord (insert ⟨k, hklt⟩ B) T ++ w))) =
          ∑ B ∈ (Finset.univ.filter (fun v : Fin n => v.val < k)).powerset,
            if insert (⟨k, hklt⟩ : Fin n) B =
                Finset.univ.filter (fun v => θ.hrv v = ⟨k, hklt⟩) then
              a (B.card + 1) * mountainScan a n k (θ.hrvScanContinuation k)
            else 0 := by
        apply Finset.sum_congr rfl
        intro B hB
        exact peak_term a θ hforward k hklt B (Finset.mem_powerset.mp hB)
      rw [mountainScan_succ_of_lt a hklt, prod_filter_lt_succ a θ k hklt, ← hprev, hpeak]
      by_cases hroot : θ.hrv ⟨k, hklt⟩ = ⟨k, hklt⟩
      · have hrF : (⟨k, hklt⟩ : Fin n) ∈ Finset.univ.filter (fun v => θ.hrv v = ⟨k, hklt⟩) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hroot⟩
        have hmem : (Finset.univ.filter (fun v => θ.hrv v = ⟨k, hklt⟩)).erase ⟨k, hklt⟩ ∈
            (Finset.univ.filter (fun v : Fin n => v.val < k)).powerset := by
          apply Finset.mem_powerset.mpr
          intro v hv
          obtain ⟨hvne, hvF⟩ := Finset.mem_erase.mp hv
          have hle : v ≤ ⟨k, hklt⟩ := θ.hrvFiber_max_le hforward ⟨k, hklt⟩ hvF
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Fin.lt_def.mp (lt_of_le_of_ne hle hvne)⟩
        have hsum : (∑ B ∈ (Finset.univ.filter (fun v : Fin n => v.val < k)).powerset,
            if insert (⟨k, hklt⟩ : Fin n) B =
                Finset.univ.filter (fun v => θ.hrv v = ⟨k, hklt⟩) then
              a (B.card + 1) * mountainScan a n k (θ.hrvScanContinuation k)
            else 0) =
            a ((Finset.univ.filter (fun v => θ.hrv v = ⟨k, hklt⟩)).card) *
              mountainScan a n k (θ.hrvScanContinuation k) := by
          rw [Finset.sum_eq_single_of_mem _ hmem]
          · rw [ite_eq_left (Finset.insert_erase hrF), Finset.card_erase_add_one hrF]
          · intro B hB hBne
            apply ite_eq_right
            intro hins
            apply hBne
            have hrB : (⟨k, hklt⟩ : Fin n) ∉ B :=
              fun h => mk_notMem_filter_lt k hklt ((Finset.mem_powerset.mp hB) h)
            rw [← hins, Finset.erase_insert hrB]
        rw [skip_term_eq_zero_of_root a θ k hklt hroot, hsum, zero_add, mul_comm]
      · have hF : Finset.univ.filter (fun v => θ.hrv v = ⟨k, hklt⟩) = ∅ :=
          θ.hrvFiber_eq_empty_of_hrv_ne hforward ⟨k, hklt⟩ hroot
        have hsupp : θ.hrvInitialSupport (k + 1) = θ.hrvInitialSupport k := by
          rw [θ.hrvInitialSupport_succ k hklt, hF, Finset.union_empty]
        have hfun : (θ.hrvScanContinuation (k + 1) : List (Fin n) → K) =
            θ.hrvScanContinuation k := by
          funext w
          simp only [hrvScanContinuation, hsupp]
        have hsum : (∑ B ∈ (Finset.univ.filter (fun v : Fin n => v.val < k)).powerset,
            if insert (⟨k, hklt⟩ : Fin n) B =
                Finset.univ.filter (fun v => θ.hrv v = ⟨k, hklt⟩) then
              a (B.card + 1) * mountainScan a n k (θ.hrvScanContinuation k)
            else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro B _
          apply ite_eq_right
          rw [hF]
          exact Finset.insert_ne_empty _ _
        rw [hfun, hsum, hF, Finset.card_empty, ha0, add_zero, mul_one]

/-- The literal per-state scan identity at an HRV cutoff, with the indicator written out. -/
theorem mountainScan_hrvInitialSupport (θ : Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) (a : ℕ → K) (ha0 : a 0 = 1)
    (k : ℕ) (hk : k ≤ n) :
    mountainScan a n k (fun w =>
      if fullOn (θ.hrvInitialSupport k) w ∧ wordCompatible (D.edgeData.selected θ.val) w
        then 1 else 0) =
      ∏ r ∈ Finset.univ.filter (fun r : Fin n => r.val < k),
        a ((Finset.univ.filter (fun v => θ.hrv v = r)).card) :=
  θ.mountainScan_hrvScanContinuation hforward a ha0 k hk

/-- At the full cutoff, the scan of full compatible words is the product over all HRV fibers. -/
theorem mountainScan_fullWord_compatible (θ : Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) (a : ℕ → K) (ha0 : a 0 = 1) :
    mountainScan a n n (fun w =>
      if fullWord w ∧ wordCompatible (D.edgeData.selected θ.val) w then 1 else 0) =
      ∏ r : Fin n, a ((Finset.univ.filter (fun v => θ.hrv v = r)).card) := by
  simpa only [θ.hrvInitialSupport_n, fullOn_univ,
    Finset.filter_true_of_mem (fun (r : Fin n) _ => r.isLt)] using
    θ.mountainScan_hrvInitialSupport hforward a ha0 n le_rfl

end VerticalStripLLT.Circular.Orientation
