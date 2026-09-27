import VerticalStripLLT.Components.MountainCauchy
import VerticalStripLLT.Components.FiniteWordCauchy
import VerticalStripLLT.Components.ElementaryScalars
import VerticalStripLLT.Components.MountainWords
import VerticalStripLLT.Components.WordOrderEmbedding
import VerticalStripLLT.Components.WordProductExpansion
import Mathlib.Order.Fin.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The finite-alphabet one-peak mountain expansion

The natural-number commutator expansion is reindexed by subsets of actual finite
vertices below the peak. Scalar coefficients remain explicit tensor factors;
no multiplicativity of a word functional is used.
-/

namespace VerticalStripLLT.Components

open scoped BigOperators TensorProduct
open Classical

noncomputable section

variable {K : Type*} [CommRing K]

local instance mountainPeakTensorRing (N : ℕ) : Ring (K ⊗[ℤ] WordAlgebra (Fin N)) :=
  Algebra.TensorProduct.instRing

private theorem finiteLetter_val (N : ℕ) (v : Fin N) :
    finiteLetter (K := K) N v.val = scalarWord K [v] := by
  simp [finiteLetter, v.isLt]

private theorem finiteLetter_prod_map_val {N : ℕ} (L : List (Fin N)) :
    ((L.map Fin.val).map (finiteLetter (K := K) N)).prod = scalarWord K L := by
  induction L with
  | nil => simp [scalarWord, algebraWord_nil, Algebra.TensorProduct.one_def]
  | cons v L ih =>
    simp only [List.map_cons, List.prod_cons, finiteLetter_val, ih]
    exact (scalarWord_append K [v] L).symm

private theorem incWord_image_val {N : ℕ} (B : Finset (Fin N)) :
    incWord (B.image Fin.val) = (incWord B).map Fin.val := by
  have he : ((Fin.valOrderEmb N).toEmbedding : Fin N → ℕ) = Fin.val := rfl
  have ho : (Fin.valOrderEmb N : Fin N → ℕ) = Fin.val := rfl
  simpa only [Finset.map_eq_image, he, ho] using
    incWord_map_orderEmbedding (Fin.valOrderEmb N) B

private theorem decWord_image_val {N : ℕ} (B : Finset (Fin N)) :
    decWord (B.image Fin.val) = (decWord B).map Fin.val := by
  have he : ((Fin.valOrderEmb N).toEmbedding : Fin N → ℕ) = Fin.val := rfl
  have ho : (Fin.valOrderEmb N : Fin N → ℕ) = Fin.val := rfl
  simpa only [Finset.map_eq_image, he, ho] using
    decWord_map_orderEmbedding (Fin.valOrderEmb N) B

private theorem sum_powerset_image_val {N : ℕ} {A : Type*} [AddCommMonoid A]
    (B : Finset (Fin N)) (f : Finset ℕ → A) :
    (∑ T ∈ (B.image Fin.val).powerset, f T) =
      ∑ T ∈ B.powerset, f (T.image Fin.val) := by
  rw [Finset.powerset_image, Finset.sum_image]
  exact (Finset.image_injective Fin.val_injective).injOn

private theorem finite_mountain_word {N : ℕ} (B T : Finset (Fin N))
    (r : Fin N) (hT : T ⊆ B) (hr : ∀ v ∈ B, v < r) :
    ((incWord (B.image Fin.val \ T.image Fin.val)).map
        (finiteLetter (K := K) N)).prod * finiteLetter (K := K) N r.val *
      ((decWord (T.image Fin.val)).map (finiteLetter (K := K) N)).prod =
        scalarWord K (blockWord (insert r B) T) := by
  rw [← Finset.image_sdiff B T Fin.val_injective, incWord_image_val, decWord_image_val,
    finiteLetter_prod_map_val, finiteLetter_prod_map_val, finiteLetter_val,
    blockWord_insert_max B T r hT hr, scalarWord_append, scalarWord_append]

private theorem elementary_sign_scalarWord (xs : List K) (N d t : ℕ)
    (L : List (Fin N)) :
    elementaryScalar (scalarAlphabet xs N) d *
        ((-1 : K ⊗[ℤ] WordAlgebra (Fin N)) ^ t * scalarWord K L) =
      (elementaryScalar xs d * (-1 : K) ^ t) ⊗ₜ[ℤ] algebraWord L := by
  change elementaryScalar
    (xs.map (algebraMap K (K ⊗[ℤ] WordAlgebra (Fin N)))) d * _ = _
  rw [elementaryScalar_map]
  have hsign : (-1 : K ⊗[ℤ] WordAlgebra (Fin N)) ^ t =
      algebraMap K (K ⊗[ℤ] WordAlgebra (Fin N)) ((-1 : K) ^ t) := by
    rw [map_pow, map_neg, map_one]
  rw [hsign, ← mul_assoc, ← map_mul]
  simp [scalarWord, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- The one-peak Cauchy factor is the finite signed sum of actual block words. -/
theorem finiteMountainPeak (xs : List K) (N k : ℕ) (hk : k < N) :
    (∑ j ∈ Finset.range xs.length,
      elementaryScalar (scalarAlphabet xs N) (j + 1) *
        adPow (letterSum (finiteLetter (K := K) N) k) (finiteLetter (K := K) N k) j) =
      ∑ B ∈ (Finset.univ.filter (fun v : Fin N => v.val < k)).powerset,
        ∑ T ∈ B.powerset,
          (elementaryScalar xs (B.card + 1) * (-1 : K) ^ T.card) ⊗ₜ[ℤ]
            algebraWord (blockWord (insert (⟨k, hk⟩ : Fin N) B) T) := by
  have h := elementary_adPow_eq_powerset_mountain (finiteLetter (K := K) N) k
    (finiteLetter_sandwich N) (finiteLetter_triple N) (scalarAlphabet xs N)
  have hlength : (scalarAlphabet xs N).length = xs.length := by simp [scalarAlphabet]
  rw [hlength] at h
  rw [h]
  let S : Finset (Fin N) := Finset.univ.filter fun v => v.val < k
  have hS : S.image Fin.val = Finset.range k := by
    ext i
    constructor
    · intro hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hv).2
    · intro hi
      have hik := Finset.mem_range.mp hi
      exact Finset.mem_image.mpr
        ⟨⟨i, hik.trans hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hik⟩, rfl⟩
  rw [← hS, sum_powerset_image_val]
  apply Finset.sum_congr rfl
  intro B hB
  rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.mul_sum,
    sum_powerset_image_val]
  apply Finset.sum_congr rfl
  intro T hT
  have hr : ∀ v ∈ B, v < (⟨k, hk⟩ : Fin N) := by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_powerset.mp hB hv)).2
  rw [Finset.card_image_of_injective _ Fin.val_injective,
    finite_mountain_word B T ⟨k, hk⟩ (Finset.mem_powerset.mp hT) hr]
  exact elementary_sign_scalarWord xs N (B.card + 1) T.card _

end

end VerticalStripLLT.Components
