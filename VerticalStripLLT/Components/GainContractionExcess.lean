import VerticalStripLLT.Components.GainContraction

/-! Endpoint balance and signed gain excess survive balanced-edge contraction. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace VerticalStripLLT.Components.GainData

open Classical

noncomputable section

variable {V E : Type*} [DecidableEq E] (G : GainData V E)

private theorem filter_loop_count {W : Type*} (f g : E → W) (F : Finset E)
    (heq : ∀ e ∈ F, f e = g e) (L : List E) (v : W) :
    (L.map f).count v + ((L.filter (fun e => decide (e ∉ F))).map g).count v =
      ((L.filter (fun e => decide (e ∉ F))).map f).count v + (L.map g).count v := by
  induction L with
  | nil => simp
  | cons e L ih =>
    by_cases he : e ∈ F
    · simp only [List.map_cons, List.filter_cons, he, not_true_eq_false,
        decide_false, Bool.false_eq_true, reduceIte, heq e he, List.count_cons]
      lia
    · simp only [List.map_cons, List.filter_cons, he, not_false_eq_true,
        decide_true, reduceIte, List.count_cons]
      lia

/-- Removing loop occurrences preserves endpoint balance, with multiplicity. -/
theorem endpoint_perm_filter_loops (F : Finset E) (P N : List E)
    (hloop : ∀ e ∈ F, G.head e = G.tail e)
    (hperm : (P.map G.head ++ N.map G.tail).Perm
      (P.map G.tail ++ N.map G.head)) :
    (((P.filter (fun e => decide (e ∉ F))).map G.head) ++
      ((N.filter (fun e => decide (e ∉ F))).map G.tail)).Perm
      (((P.filter (fun e => decide (e ∉ F))).map G.tail) ++
        ((N.filter (fun e => decide (e ∉ F))).map G.head)) := by
  apply List.perm_iff_count.mpr
  intro v
  have h := hperm.count_eq v
  have hP := filter_loop_count G.head G.tail F hloop P v
  have hN := filter_loop_count G.head G.tail F hloop N v
  simp only [List.count_append] at h ⊢
  lia

/-- The projected excess witness retains balanced endpoints after collapsed edges are removed. -/
theorem contraction_endpoint_perm (F : Finset E) (p : V → ℤ) (P N : List E)
    (hperm : (P.map G.head ++ N.map G.tail).Perm
      (P.map G.tail ++ N.map G.head)) :
    let H := G.contraction F p
    (((P.filter (fun e => decide (e ∉ F))).map H.head) ++
      ((N.filter (fun e => decide (e ∉ F))).map H.tail)).Perm
      (((P.filter (fun e => decide (e ∉ F))).map H.tail) ++
        ((N.filter (fun e => decide (e ∉ F))).map H.head)) := by
  apply (G.contraction F p).endpoint_perm_filter_loops F P N
  · intro e he
    exact (G.contraction_tail_eq_head p he).symm
  · simpa only [List.map_append, List.map_map, Function.comp_def] using
      hperm.map (G.weakBlockMk F)

omit [DecidableEq E] in
private theorem sum_map_sub' (L : List E) (f g : E → ℤ) :
    (L.map (fun e => f e - g e)).sum = (L.map f).sum - (L.map g).sum := by
  induction L with
  | nil => simp
  | cons e L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem filter_zero_sum (F : Finset E) (f : E → ℤ)
    (hf : ∀ e ∈ F, f e = 0) (L : List E) :
    ((L.filter (fun e => decide (e ∉ F))).map f).sum = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons e L ih =>
    by_cases he : e ∈ F
    · simpa [he, hf e he] using ih
    · simpa [he] using ih

/-- The signed gain difference is unchanged by contraction and removal of balanced edges. -/
theorem contraction_gain_excess_eq {F : Finset E} {p : V → ℤ}
    (hp : G.BalancedPotential F p) (P N : List E)
    (hperm : (P.map G.head ++ N.map G.tail).Perm
      (P.map G.tail ++ N.map G.head)) :
    let H := G.contraction F p
    (((P.filter (fun e => decide (e ∉ F))).map H.gain).sum -
      ((N.filter (fun e => decide (e ∉ F))).map H.gain).sum) =
      (P.map G.gain).sum - (N.map G.gain).sum := by
  dsimp only
  have hz : ∀ e ∈ F, (G.contraction F p).gain e = 0 :=
    fun e he => G.contraction_gain_eq_zero hp he
  rw [filter_zero_sum F _ hz, filter_zero_sum F _ hz]
  have ht := (hperm.map p).sum_eq
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def] at ht
  change (P.map (fun e => G.gain e - (p (G.head e) - p (G.tail e)))).sum -
    (N.map (fun e => G.gain e - (p (G.head e) - p (G.tail e)))).sum = _
  simp only [sum_map_sub']
  lia

/-- The abstract cancellation instantiated on the actual balanced contraction. -/
theorem contraction_sum_cyclicNegative_eq_zero [Fintype V]
    {F : Finset E} {p : V → ℤ} (hp : G.BalancedPotential F p)
    (A N : Finset E) (P Nsteps : List E)
    (hN : ∀ e ∈ Nsteps, e ∈ N) (hcover : ∀ e ∈ N, e ∈ Nsteps)
    (hP : ∀ e ∈ P, e ∈ A)
    (hperm : (P.map G.head ++ Nsteps.map G.tail).Perm
      (P.map G.tail ++ Nsteps.map G.head))
    (hexcess : (Nsteps.map G.gain).sum < (P.map G.gain).sum) :
    let H := G.contraction F p
    (∑ J ∈ (N \ F).powerset,
      if H.SimpleCyclesNegative ((A \ F) ∪ J) ∧
          OrderedPartitions.TotallyCyclic (H.selectedRelation ((A \ F) ∪ J))
      then (-1 : ℤ) ^ (J.card +
        OrderedPartitions.weakComponentCount (H.selectedRelation ((A \ F) ∪ J)))
      else 0) = 0 := by
  let P' := P.filter (fun e => decide (e ∉ F))
  let N' := Nsteps.filter (fun e => decide (e ∉ F))
  apply (G.contraction F p).sum_powerset_cyclicNegative_eq_zero_of_gain_excess
    (A \ F) (N \ F) P' N'
  · intro e he
    obtain ⟨heN, heF⟩ := List.mem_filter.mp he
    exact Finset.mem_sdiff.mpr ⟨hN e heN, of_decide_eq_true heF⟩
  · intro e he
    exact List.mem_filter.mpr ⟨hcover e (Finset.mem_sdiff.mp he).1,
      decide_eq_true (Finset.mem_sdiff.mp he).2⟩
  · intro e he
    obtain ⟨heP, heF⟩ := List.mem_filter.mp he
    exact Finset.mem_sdiff.mpr ⟨hP e heP, of_decide_eq_true heF⟩
  · simpa only [P', N', decide_not] using
      G.contraction_endpoint_perm F p P Nsteps hperm
  · have h := G.contraction_gain_excess_eq hp P Nsteps hperm
    change (N'.map (G.contraction F p).gain).sum <
      (P'.map (G.contraction F p).gain).sum
    dsimp only [P', N']
    dsimp only at h
    lia

end

end VerticalStripLLT.Components.GainData
