import VerticalStripLLT.BounceAgreement
import VerticalStripLLT.FirstEastCases
import VerticalStripLLT.ColumnCharacterization
import VerticalStripLLT.ProductReduction
import VerticalStripLLT.NorthPredecessor

namespace VerticalStripLLT

open Step

namespace SatisfiesReductionRecursion

/-- Uniqueness for the sufficient reduction certificate, by size, east count,
and first-east height. -/
theorem unique {K : Type*} [CommRing K] [IsDomain K]
    {q : K} {e : ℕ → K} {F G : ∀ n, SchroderPath n → K}
    (H : SatisfiesReductionRecursion q e F)
    (HG : SatisfiesReductionRecursion q e G) (hq : q - 1 ≠ 0) :
    ∀ n (P : SchroderPath n), F n P = G n P := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ihn =>
      suffices ∀ c h (P : SchroderPath n), eastCount P.steps = c →
          firstEastHeight P.steps = h → F n P = G n P from
        fun P => this _ _ P rfl rfl
      intro c
      induction c using Nat.strong_induction_on with
      | h c ihc =>
          intro height
          induction height using Nat.strong_induction_on with
          | h height ihheight =>
              intro P hc hh
              by_cases hn : n = 0
              · subst n
                have hp := (SchroderPath.steps_eq_nil_iff P).mpr rfl
                have hf := SchroderPath.invariant_congr F P SchroderPath.empty rfl hp
                have hg := SchroderPath.invariant_congr G P SchroderPath.empty rfl hp
                rw [hf, hg, H.empty, HG.empty]
              by_cases hone : eastCount P.steps = 1
              · obtain ⟨k, hk, hsize⟩ := valid_one_east_column_size P hone
                have hf := SchroderPath.invariant_congr F P (SchroderPath.column k) hsize hk
                have hg := SchroderPath.invariant_congr G P (SchroderPath.column k) hsize hk
                rw [hf, hg, H.column, HG.column]
              have he := P.east_mem_of_pos (Nat.pos_of_ne_zero hn)
              have hpositive : 0 < eastCount P.steps := List.count_pos_iff.mpr he
              obtain ⟨Y, W, hword, hY⟩ := exists_east_decomposition he
              have hv : validFrom n 0 0 (Y ++ east :: W) = true := by
                rw [← hword]
                exact P.valid
              have hcount : 2 ≤ eastCount (Y ++ east :: W) := by
                rw [← hword]
                lia
              have hcw : eastCount (Y ++ east :: W) = c := by rw [← hword]; exact hc
              have hhw : firstEastHeight (Y ++ east :: W) = height := by
                rw [← hword]
                exact hh
              have hf := SchroderPath.invariant_congr F P ⟨Y ++ east :: W, hv⟩ rfl hword
              have hg := SchroderPath.invariant_congr G P ⟨Y ++ east :: W, hv⟩ rfl hword
              rw [hf, hg]
              have hsmall (Q : SchroderPath n)
                  (hcQ : eastCount Q.steps = eastCount (Y ++ east :: W))
                  (hhQ : firstEastHeight Q.steps < firstEastHeight (Y ++ east :: W)) :
                  F n Q = G n Q :=
                ihheight _ (by rw [← hhw]; exact hhQ) Q (hcQ.trans hcw) rfl
              rcases firstEast_prefix_cases Y W hv hY with hreturn | hnorth | hseed
              · obtain ⟨k, l, Q, R, _, _, hk, hl, hsize, hQ, hR, hval⟩ :=
                  firstEast_product_reduction q e F H.toSatisfiesRecursion
                    Y W hv hY hreturn hcount
                have hG := SchroderPath.invariant_congr G
                  (⟨Y ++ east :: W, hv⟩ : SchroderPath n) (Q.concat R) hsize.symm
                  (by simp only [SchroderPath.concat_steps, hQ, hR,
                    List.append_assoc, List.singleton_append])
                rw [HG.concat] at hG
                rw [hval, hG, ihn k hk Q, ihn l hl R]
              · obtain ⟨U, hU, hno, hgap⟩ := hnorth
                have hvn : validFrom n 0 0 (U ++ north :: east :: W) = true := by
                  simpa only [hU, List.append_assoc, List.singleton_append] using hv
                obtain ⟨Q, R, hQ, hR, hQc, hRc, hRh, hval⟩ :=
                  firstEast_north_reduction q e F H.toSatisfiesRecursion U W hvn hno hgap
                obtain ⟨Q', R', hQ', hR', _, _, _, hgval⟩ :=
                  firstEast_north_reduction q e G HG.toSatisfiesRecursion U W hvn hno hgap
                have hQG : G n Q' = G n Q :=
                  SchroderPath.invariant_congr G Q' Q rfl (hQ'.trans hQ.symm)
                have hRG : G n R' = G n R :=
                  SchroderPath.invariant_congr G R' R rfl (hR'.trans hR.symm)
                have heqn : Y ++ east :: W = U ++ north :: east :: W := by
                  simp only [hU, List.append_assoc, List.singleton_append]
                have hQc' : eastCount Q.steps < c := by
                  rw [heqn] at hcw
                  lia
                have hiQ := ihc _ hQc' (firstEastHeight Q.steps) Q rfl rfl
                have hiR : F n R = G n R := hsmall R
                  (by rw [heqn]; exact hRc.symm)
                  (by rw [heqn, hRh]; exact Nat.lt_succ_self _)
                have hFn := SchroderPath.invariant_congr F
                  (⟨Y ++ east :: W, hv⟩ : SchroderPath n) ⟨_, hvn⟩ rfl heqn
                have hGn := SchroderPath.invariant_congr G
                  (⟨Y ++ east :: W, hv⟩ : SchroderPath n) ⟨_, hvn⟩ rfl heqn
                rw [hFn, hGn, hval, hgval, hQG, hRG, hiQ, hiR]
              · exact H.bounce_agreement HG hq hseed hv hsmall

end SatisfiesReductionRecursion

end VerticalStripLLT
