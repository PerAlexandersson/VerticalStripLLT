import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.Rev

/-! Order embeddings and image predicates under finite order reversal. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

def reverseOrderEmbedding {k n : ℕ} (ι : Fin k ↪o Fin n) : Fin k ↪o Fin n :=
  OrderEmbedding.ofStrictMono (fun i => (ι i.rev).rev) (by
    intro i j hij
    apply Fin.rev_lt_rev.mpr
    exact ι.strictMono (Fin.rev_lt_rev.mpr hij))

@[simp] theorem reverseOrderEmbedding_apply {k n : ℕ} (ι : Fin k ↪o Fin n)
    (i : Fin k) : reverseOrderEmbedding ι i = (ι i.rev).rev :=
  rfl

theorem reverseOrderEmbedding_involutive {k n : ℕ} (ι : Fin k ↪o Fin n) :
    reverseOrderEmbedding (reverseOrderEmbedding ι) = ι := by
  apply DFunLike.ext
  intro i
  simp only [reverseOrderEmbedding_apply, Fin.rev_rev]

theorem exists_reverseOrderEmbedding_iff {k n : ℕ} (ι : Fin k ↪o Fin n)
    (z : Fin n) :
    (∃ w, reverseOrderEmbedding ι w = z) ↔ ∃ w, ι w = z.rev := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.rev, ?_⟩
    have := congrArg Fin.rev hw
    simpa only [reverseOrderEmbedding_apply, Fin.rev_rev] using this
  · rintro ⟨w, hw⟩
    refine ⟨w.rev, ?_⟩
    have := congrArg Fin.rev hw
    simpa only [reverseOrderEmbedding_apply, Fin.rev_rev] using this

theorem reverseOrderEmbedding_prefix_image
    {k n : ℕ} (ι : Fin k ↪o Fin n) {c a : Fin n}
    (himage : ∀ z, (∃ w, ι w = z) ↔ c ≤ z ∨ z = a) :
    ∀ z, (∃ w, reverseOrderEmbedding ι w = z) ↔
      z ≤ c.rev ∨ z = a.rev := by
  intro z
  rw [exists_reverseOrderEmbedding_iff]
  rw [himage]
  constructor
  · rintro (hc | ha)
    · exact Or.inl (Fin.le_rev_iff.mpr hc)
    · exact Or.inr (Fin.rev_eq_iff.mp ha)
  · rintro (hc | ha)
    · exact Or.inl (Fin.le_rev_iff.mp hc)
    · exact Or.inr (Fin.rev_eq_iff.mpr ha)

end VerticalStripLLT.Circular.DiagramProof
