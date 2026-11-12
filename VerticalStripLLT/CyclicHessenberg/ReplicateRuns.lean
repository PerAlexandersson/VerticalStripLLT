import VerticalStripLLT.CyclicHessenberg.ColorRuns

set_option autoImplicit false

/-! Equality runs of a strictly increasing color list with positive block sizes. -/

namespace VerticalStripLLT.CyclicHessenberg

open List

variable {C : Type*} [LinearOrder C]

def constantBlocks (colors : List C) (sizes : List ℕ) : List (List C) :=
  (colors.zip sizes).map fun p => List.replicate p.2 p.1

theorem constantBlocks_lengths (colors : List C) (sizes : List ℕ)
    (hlen : colors.length = sizes.length) :
    (constantBlocks colors sizes).map List.length = sizes := by
  induction colors generalizing sizes with
  | nil =>
    cases sizes with
    | nil => rfl
    | cons n ns => simp at hlen
  | cons c cs ih =>
    cases sizes with
    | nil => simp at hlen
    | cons n ns =>
      have htail : cs.length = ns.length := Nat.succ.inj hlen
      simp [constantBlocks, htail, ih htail]

theorem constantBlocks_flatten_length (colors : List C) (sizes : List ℕ)
    (hlen : colors.length = sizes.length) :
    (constantBlocks colors sizes).flatten.length = sizes.sum := by
  rw [List.length_flatten, constantBlocks_lengths colors sizes hlen]

private def runSeparated (u v : List C) : Prop :=
  ∃ hu : u ≠ [], ∃ hv : v ≠ [],
    decide (u.getLast hu = v.head hv) = false

private theorem replicate_ne_nil_of_pos (a : C) {n : ℕ} (hn : 0 < n) :
    List.replicate n a ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  simp at hlen
  exact (Nat.ne_of_gt hn) hlen

private theorem replicate_last_of_pos (a : C) {n : ℕ} (hn : 0 < n) :
    ∀ h : List.replicate n a ≠ [], (List.replicate n a).getLast h = a := by
  intro h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa using List.getLast_replicate_succ m a

private theorem replicate_head_of_pos (a : C) {n : ℕ} (hn : 0 < n) :
    ∀ h : List.replicate n a ≠ [], (List.replicate n a).head h = a := by
  intro h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp

private theorem replicate_runSeparated (a b : C) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hab : a < b) :
    runSeparated (List.replicate n a) (List.replicate m b) := by
  have hu := replicate_ne_nil_of_pos a hn
  have hv := replicate_ne_nil_of_pos b hm
  refine ⟨hu, hv, ?_⟩
  rw [replicate_last_of_pos a hn hu, replicate_head_of_pos b hm hv]
  simp [ne_of_lt hab]

private theorem zip_pairwise_lt_pos (colors : List C) (sizes : List ℕ)
    (hcolor : colors.Pairwise (· < ·)) (hpos : ∀ n ∈ sizes, 0 < n) :
    (colors.zip sizes).Pairwise
      (fun p q => p.1 < q.1 ∧ 0 < p.2 ∧ 0 < q.2) := by
  induction colors generalizing sizes with
  | nil => simp
  | cons c cs ih =>
    cases sizes with
    | nil => simp
    | cons n ns =>
      have hhead := (List.pairwise_cons.mp hcolor).1
      have htail := (List.pairwise_cons.mp hcolor).2
      have hn := hpos n (by simp)
      simp only [List.zip_cons_cons, List.pairwise_cons]
      constructor
      · intro p hp
        have hp' := List.of_mem_zip hp
        exact ⟨hhead p.1 hp'.1, hn, hpos p.2 hp'.2⟩
      · apply ih htail
        intro m hm
        exact hpos m (by simp [hm])

private theorem constantBlocks_pairwise_separated (colors : List C) (sizes : List ℕ)
    (hcolor : colors.Pairwise (· < ·)) (hpos : ∀ n ∈ sizes, 0 < n) :
    (constantBlocks colors sizes).Pairwise runSeparated := by
  unfold constantBlocks
  rw [List.pairwise_map]
  apply (zip_pairwise_lt_pos colors sizes hcolor hpos).imp
  intro p q hpq
  exact replicate_runSeparated p.1 q.1 p.2 q.2 hpq.1 hpq.2.1 hpq.2.2

theorem equalityRuns_flatten_constantBlocks (colors : List C) (sizes : List ℕ)
    (hlen : colors.length = sizes.length) (hcolor : colors.Pairwise (· < ·))
    (hpos : ∀ n ∈ sizes, 0 < n) :
    List.equalityRuns (constantBlocks colors sizes).flatten =
      constantBlocks colors sizes := by
  classical
  let blocks := constantBlocks colors sizes
  have hnonempty : [] ∉ blocks := by
    intro h
    obtain ⟨p, hp, hpEq⟩ := List.mem_map.mp (show [] ∈ blocks from h)
    have hz : p.2 = 0 := by
      have hlen' := congrArg List.length hpEq
      simpa using hlen'
    exact (Nat.ne_of_gt (hpos p.2 (List.of_mem_zip hp).2)) hz
  have hchain : ∀ b ∈ blocks,
      b.IsChain (fun a c => decide (a = c)) := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    exact List.isChain_replicate_of_rel p.2 (by simp)
  have hseparated : blocks.IsChain runSeparated := by
    exact (constantBlocks_pairwise_separated colors sizes hcolor hpos).isChain
  change List.splitBy (fun a b => decide (a = b)) blocks.flatten = blocks
  exact List.splitBy_flatten hnonempty hchain hseparated

/-- Constant blocks whose colors increase concatenate to a nondecreasing word. -/
theorem constantBlocks_flatten_pairwise_le (colors : List C) (sizes : List ℕ)
    (hc : colors.Pairwise (· < ·)) :
    (constantBlocks colors sizes).flatten.Pairwise (· ≤ ·) := by
  induction colors generalizing sizes with
  | nil => simp [constantBlocks]
  | cons c cs ih =>
    cases sizes with
    | nil => simp [constantBlocks]
    | cons d ds =>
      have hc' := List.pairwise_cons.mp hc
      change (List.replicate d c ++ (constantBlocks cs ds).flatten).Pairwise (· ≤ ·)
      apply List.pairwise_append.mpr
      refine ⟨by simp, ih ds hc'.2, ?_⟩
      intro x hx y hy
      have hxc := (List.mem_replicate.mp hx).2
      obtain ⟨b, hb, hyb⟩ := List.mem_flatten.mp hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
      have hyp := (List.mem_replicate.mp hyb).2
      rw [hxc, hyp]
      exact (hc'.1 _ (List.of_mem_zip hp).1).le

end VerticalStripLLT.CyclicHessenberg
