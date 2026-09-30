import Mathlib.Combinatorics.SimpleGraph.Paths

/-! A simple path can be split around an internal vertex. -/

namespace VerticalStripLLT.Circular.DiagramProof

open SimpleGraph

theorem exists_path_split_at_internal_vertex
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v b : V}
    (p : G.Walk u v) (hp : p.IsPath) (hb : b ∈ p.support)
    (hbu : b ≠ u) (hbv : b ≠ v) :
    ∃ i j, ∃ p₁ : G.Walk u i, ∃ p₂ : G.Walk j v,
      G.Adj i b ∧ G.Adj b j ∧ i ≠ j ∧
        (∀ x, x ∈ p₁.support → x ∈ p.support ∧ x ≠ b) ∧
        (∀ x, x ∈ p₂.support → x ∈ p.support ∧ x ≠ b) := by
  obtain ⟨q, r, hq, hr, hpqr⟩ := hp.mem_support_iff_exists_append.mp hb
  have hqnil : ¬q.Nil := by
    intro hnil
    exact hbu (hq.nil_iff_eq.mp hnil).symm
  have hrnil : ¬r.Nil := by
    intro hnil
    exact hbv (hr.nil_iff_eq.mp hnil)
  have hpqr_path : (q.append r).IsPath := by
    rw [← hpqr]
    exact hp
  have hqnot : b ∉ q.dropLast.support := by
    rw [q.support_dropLast hqnil]
    have hnodup := hq.support_nodup
    rw [← q.dropLast_support_concat] at hnodup
    exact ((List.nodup_concat _ _).mp
      (by simpa only [List.concat_eq_append] using hnodup)).1
  have hrnot : b ∉ r.tail.support := by
    have hnodup := hr.support_nodup
    rw [← r.cons_support_tail hrnil] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hiq : q.penultimate ∈ q.support :=
    List.mem_of_mem_dropLast (q.penultimate_mem_dropLast_support hqnil)
  have hjtail : r.snd ∈ r.tail.support := by
    rw [r.support_tail_of_not_nil hrnil]
    exact r.snd_mem_tail_support hrnil
  have hjr : r.snd ∈ r.support := by
    rw [← r.cons_support_tail hrnil]
    exact List.mem_cons_of_mem _ hjtail
  have hjb : r.snd ≠ b := by
    intro h
    apply hrnot
    simpa [h] using hjtail
  refine ⟨q.penultimate, r.snd, q.dropLast, r.tail, q.adj_penultimate hqnil,
    r.adj_snd hrnil, hpqr_path.ne_of_mem_support_of_append hjb hiq hjr, ?_, ?_⟩
  · intro x hx
    constructor
    · rw [hpqr]
      apply q.support_subset_support_append_left r
      rw [q.support_dropLast hqnil] at hx
      exact List.mem_of_mem_dropLast hx
    · exact fun heq => hqnot (heq ▸ hx)
  · intro x hx
    constructor
    · rw [hpqr]
      apply q.support_subset_support_append_right r
      rw [r.support_tail_of_not_nil hrnil] at hx
      exact List.mem_of_mem_tail hx
    · exact fun heq => hrnot (heq ▸ hx)

end VerticalStripLLT.Circular.DiagramProof
