import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Hom.Basic

/-! Order embeddings for finite subsets and their initial segments. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

theorem exists_orderEmbedding_of_nonempty_finset
    {n : ℕ} (s : Finset (Fin n)) (hs : s.Nonempty) :
    ∃ k, ∃ ι : Fin (k + 1) ↪o Fin n,
      ∀ z, (∃ i, ι i = z) ↔ z ∈ s := by
  let k : ℕ := s.card - 1
  have hcard : s.card = k + 1 := by
    dsimp [k]
    exact (Nat.sub_add_cancel (Finset.card_pos.mpr hs)).symm
  let e := s.orderIsoOfFin hcard
  let ι : Fin (k + 1) ↪o Fin n :=
    OrderEmbedding.ofStrictMono (fun i => (e i).val) (by
      intro i j hij
      exact e.strictMono hij)
  refine ⟨k, ι, ?_⟩
  intro z
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).property
  · intro hz
    obtain ⟨w, hw⟩ := e.surjective ⟨z, hz⟩
    refine ⟨w, ?_⟩
    exact congrArg Subtype.val hw

/-- The preimage of `{z | z ≤ c}` under an order embedding is an initial segment. -/
theorem exists_initial_segment_of_orderEmbedding
    {k n : ℕ} (ι : Fin (k + 1) ↪o Fin n) (c : Fin n)
    (hc : ∃ i, ι i ≤ c) :
    ∃ t : Fin (k + 1), ∀ i, ι i ≤ c ↔ i ≤ t := by
  let q : Finset (Fin (k + 1)) :=
    Finset.univ.filter (fun i => ι i ≤ c)
  have hq : q.Nonempty := by
    obtain ⟨i, hi⟩ := hc
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let t : Fin (k + 1) := q.max' hq
  refine ⟨t, ?_⟩
  intro i
  constructor
  · intro hi
    exact Finset.le_max' q i (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hi⟩)
  · intro hit
    have ht : ι t ≤ c := (Finset.mem_filter.mp (q.max'_mem hq)).2
    exact (ι.monotone hit).trans ht

end

end VerticalStripLLT.Circular.DiagramProof
