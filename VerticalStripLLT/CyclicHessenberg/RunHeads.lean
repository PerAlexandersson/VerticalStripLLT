import VerticalStripLLT.CyclicHessenberg.ColorRuns
import VerticalStripLLT.CyclicHessenberg.ReplicateRuns

/-! Recover constant blocks from their heads and positive lengths. -/

namespace VerticalStripLLT.CyclicHessenberg

variable {C : Type*} [LinearOrder C]

def blockHeads (B : List (List C)) : List C := B.filterMap List.head?

theorem pmap_heads_eq_blockHeads (B : List (List C)) (hne : ∀ b ∈ B, b ≠ []) :
    B.pmap (fun b hb => b.head hb) hne = blockHeads B := by
  induction B with
  | nil => rfl
  | cons b B ih =>
    cases b with
    | nil => exact (hne [] (by simp) rfl).elim
    | cons c cs =>
      simp only [List.pmap_cons, List.head_cons, blockHeads, List.filterMap_cons,
        List.head?_cons]
      exact congrArg (List.cons c) (ih _)

theorem blockHeads_length (B : List (List C)) (hne : ∀ b ∈ B, b ≠ []) :
    (blockHeads B).length = B.length := by
  rw [← pmap_heads_eq_blockHeads B hne, List.length_pmap]

theorem equalityRunHeads_eq_blockHeads (l : List C) :
    l.equalityRunHeads = blockHeads l.equalityRuns :=
  pmap_heads_eq_blockHeads _ _

theorem blockHeads_constantBlocks (colors : List C) (sizes : List ℕ)
    (hlen : colors.length = sizes.length) (hpos : ∀ n ∈ sizes, 0 < n) :
    blockHeads (constantBlocks colors sizes) = colors := by
  induction colors generalizing sizes with
  | nil => simp [constantBlocks, blockHeads]
  | cons c cs ih =>
    cases sizes with
    | nil => simp at hlen
    | cons d ds =>
      have hd := hpos d (by simp)
      obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
      change (List.replicate (a + 1) c :: constantBlocks cs ds).filterMap List.head? = c :: cs
      simp only [List.replicate_succ, List.filterMap_cons, List.head?_cons]
      exact congrArg (List.cons c) (ih ds (Nat.succ.inj hlen)
        (fun n hn => hpos n (List.mem_cons_of_mem _ hn)))

theorem constantBlocks_heads_lengths (B : List (List C))
    (hne : ∀ b ∈ B, b ≠ [])
    (hc : ∀ b (hb : b ∈ B), b = List.replicate b.length (b.head (hne b hb))) :
    constantBlocks (blockHeads B) (B.map List.length) = B := by
  induction B with
  | nil => rfl
  | cons b B ih =>
    cases b with
    | nil => exact (hne [] (by simp) rfl).elim
    | cons c cs =>
      have hb := hc (c :: cs) (by simp)
      change List.replicate (c :: cs).length c ::
        constantBlocks (blockHeads B) (B.map List.length) = (c :: cs) :: B
      rw [← hb]
      exact congrArg (List.cons (c :: cs)) (ih _ _)

theorem constantBlocks_equalityRuns (l : List C) :
    constantBlocks (blockHeads l.equalityRuns) (l.equalityRuns.map List.length) =
      l.equalityRuns :=
  constantBlocks_heads_lengths _ (fun _ => List.mem_equalityRun_ne_nil)
    (fun _ => List.equalityRun_eq_replicate_head)

end VerticalStripLLT.CyclicHessenberg
