import VerticalStripLLT.Polynomial
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

namespace VerticalStripLLT

open scoped BigOperators

noncomputable def specializeLast (m : ℕ) : XPoly (m + 1) →+* XPoly m :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Fin.lastCases 0 (fun i : Fin m => MvPolynomial.X i))

@[simp] theorem specializeLast_X_last (m : ℕ) :
    specializeLast m (MvPolynomial.X (Fin.last m)) = 0 := by
  simp [specializeLast]

@[simp] theorem specializeLast_X_castSucc (m : ℕ) (i : Fin m) :
    specializeLast m (MvPolynomial.X i.castSucc) = MvPolynomial.X i := by
  simp [specializeLast]

theorem specializeLast_esymm (m k : ℕ) :
    specializeLast m (MvPolynomial.esymm (Fin (m + 1)) Q k) =
      MvPolynomial.esymm (Fin m) Q k := by
  classical
  let S : Finset (Fin (m + 1)) :=
    (Finset.univ : Finset (Fin m)).map Fin.castSuccEmb
  have hlastnotS : Fin.last m ∉ S := by
    simp [S]
  have huniv : (Finset.univ : Finset (Fin (m + 1))) = insert (Fin.last m) S := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [S]
  have hmapProd (s : Finset (Fin m)) :
      specializeLast m (∏ i ∈ s.map Fin.castSuccEmb, MvPolynomial.X i) =
        ∏ i ∈ s, MvPolynomial.X i := by
    rw [map_prod, Finset.prod_map]
    simp
  have hfirst (r : ℕ) :
      specializeLast m (∑ s ∈ S.powersetCard r, ∏ i ∈ s, MvPolynomial.X i) =
        MvPolynomial.esymm (Fin m) Q r := by
    simp only [MvPolynomial.esymm, map_sum]
    dsimp only [S]
    rw [Finset.powersetCard_map, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro s hs
    exact hmapProd s
  have hzero (s : Finset (Fin (m + 1))) (hs : Fin.last m ∈ s) :
      specializeLast m (∏ i ∈ s, MvPolynomial.X i) = 0 := by
    rw [map_prod]
    exact Finset.prod_eq_zero hs (specializeLast_X_last m)
  cases k with
  | zero => simp only [MvPolynomial.esymm_zero, map_one]
  | succ k =>
    have hdisjoint : Disjoint (S.powersetCard k.succ)
        ((S.powersetCard k).image (insert (Fin.last m))) := by
      refine Finset.disjoint_left.mpr ?_
      intro s hs ht
      rcases Finset.mem_image.mp ht with ⟨u, hu, rfl⟩
      exact hlastnotS ((Finset.mem_powersetCard.mp hs).1 (Finset.mem_insert_self _ _))
    have hsecond : specializeLast m
        (∑ s ∈ (S.powersetCard k).image (insert (Fin.last m)),
          ∏ i ∈ s, MvPolynomial.X i) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro s hs
      rcases Finset.mem_image.mp hs with ⟨u, hu, rfl⟩
      exact hzero _ (Finset.mem_insert_self _ _)
    calc
      specializeLast m (MvPolynomial.esymm (Fin (m + 1)) Q k.succ) =
          specializeLast m
            ((∑ s ∈ S.powersetCard k.succ, ∏ i ∈ s, MvPolynomial.X i) +
              ∑ s ∈ (S.powersetCard k).image (insert (Fin.last m)),
                ∏ i ∈ s, MvPolynomial.X i) := by
        rw [MvPolynomial.esymm, huniv, Finset.powersetCard_succ_insert hlastnotS,
          Finset.sum_union hdisjoint]
      _ = specializeLast m (∑ s ∈ S.powersetCard k.succ, ∏ i ∈ s, MvPolynomial.X i) +
          specializeLast m (∑ s ∈ (S.powersetCard k).image (insert (Fin.last m)),
            ∏ i ∈ s, MvPolynomial.X i) := by
        rw [map_add]
      _ = MvPolynomial.esymm (Fin m) Q k.succ := by
        rw [hfirst, hsecond, add_zero]

theorem specializeLast_evalElementary (m : ℕ) :
    (specializeLast m).comp (evalElementary (m + 1)) =
      evalElementary m := by
  apply MvPolynomial.ringHom_ext
  · intro p
    simp [specializeLast, evalElementary]
  · intro k
    change specializeLast m (evalElementary (m + 1) (elementary k)) =
      evalElementary m (elementary k)
    rw [evalElementary_elementary, evalElementary_elementary, specializeLast_esymm]

end VerticalStripLLT
