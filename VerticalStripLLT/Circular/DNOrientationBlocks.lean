import VerticalStripLLT.Circular.DNTargetData
import VerticalStripLLT.Circular.HRVTriangle
import VerticalStripLLT.Circular.PeriodicSwapHRV

set_option backward.isDefEq.respectTransparency false

-- NEW MODULE VerticalStripLLT.Circular.DNOrientationBlocks

/-! The four-state blocks of the source and target DN orientation sums. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ}

/-- The triangle identity, indexed by normal endpoint pairs. -/
theorem tri_local_identity_pairs (E : Diagram n) {s g1 g2 : Edge E.area} {P Y T : ℤ}
    (hs : s ∈ E.strict) (hsL : E.naturalLift s P T) (h1L : E.naturalLift g1 P Y)
    (h2L : E.naturalLift g2 Y T) (hg1 : g1 ∉ E.strict) (hg2 : g2 ∉ E.strict)
    (Q : Finset (Fin n × Fin n)) :
    E.orientMono (E.normalOf (insert (g1.tail, g1.head) Q)) +
        E.orientMono (E.normalOf (insert (g2.tail, g2.head) Q)) =
      E.orientMono (E.normalOf Q) +
        E.orientMono (E.normalOf (insert (g2.tail, g2.head) (insert (g1.tail, g1.head) Q))) := by
  simp only [E.normalOf_insert _ hg1, E.normalOf_insert _ hg2]
  exact E.tri_local_identity hs hsL h1L h2L ((E.mem_normalEdges_iff _).mpr hg1)
    ((E.mem_normalEdges_iff _).mpr hg2) _ (E.normalOf_subset Q)

variable (D : Diagram n)

section DN

variable (e f : Edge D.area) (he : e ∈ D.strict) (hf : f ∈ D.strict) (hne : f ≠ e)
  (hcontact : f.tail = e.head)
  (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
  (hb : D.area.area e.head + 1 < n)
  (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
  (hlen : 2 ≤ f.length.val)
  (hgap : D.area.area (D.area.next f.head) < D.area.area f.head)

include he hf hcontact heq hns hlen in
/-- Source block: triangle `(i, y, z)` with the strict edge `f`. -/
theorem dn_source_local (Q : Finset (Fin n × Fin n)) :
    D.orientMono (D.normalOf (insert (e.head, D.area.next e.head) Q)) +
        D.orientMono (D.normalOf (insert (D.area.next e.head, f.head) Q)) =
      D.orientMono (D.normalOf Q) + D.orientMono (D.normalOf
        (insert (e.head, D.area.next e.head) (insert (D.area.next e.head, f.head) Q))) := by
  have h := D.tri_local_identity_pairs hf (D.dn_f_lift e f hcontact) (D.dnG_lift e he heq)
    (D.dnH_lift e f hf hcontact hlen) (D.dnG_not_strict e he heq hns)
    (D.dnH_not_strict e f hf hcontact hlen) Q
  rw [dnG_tail, dnG_head, dnH_tail, dnH_head, Finset.insert_comm] at h
  exact h

include hcontact in
/-- Target block: triangle `(a, i, y)` with the raised strict edge. -/
theorem dn_target_local (Q : Finset (Fin n × Fin n)) :
    (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).orientMono
        ((D.dnSuccessor e f he hf hne heq hb hns hlen hgap).normalOf
          (insert (e.tail, e.head) Q)) +
      (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).orientMono
        ((D.dnSuccessor e f he hf hne heq hb hns hlen hgap).normalOf
          (insert (e.head, D.area.next e.head) Q)) =
    (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).orientMono
        ((D.dnSuccessor e f he hf hne heq hb hns hlen hgap).normalOf Q) +
      (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).orientMono
        ((D.dnSuccessor e f he hf hne heq hb hns hlen hgap).normalOf
          (insert (e.tail, e.head) (insert (e.head, D.area.next e.head) Q))) := by
  set E := D.dnSuccessor e f he hf hne heq hb hns hlen hgap with hE
  have hLe := D.dn_Le e he
  have hepos := e.length_pos
  have hSt : (e.tail, D.area.next e.head) ∈ E.pairGraph.strictEdges := by
    rw [hE, dn_target_strict _ _ _ _ _ _ hcontact, dnSt']
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hN1 : (e.tail, e.head) ∈ E.pairGraph.normalEdges := by
    rw [hE, dn_target_normal _ _ _ _ _ _ hcontact]
    exact Finset.mem_insert_self _ _
  have hN2 : (e.head, D.area.next e.head) ∈ E.pairGraph.normalEdges := by
    rw [hE, dn_target_normal _ _ _ _ _ _ hcontact]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  obtain ⟨s, hs, hsp⟩ := (E.mem_pairGraph_strict_iff _).mp hSt
  obtain ⟨g1, hg1, hg1p⟩ := (E.mem_pairGraph_normal_iff _).mp hN1
  obtain ⟨g2, hg2, hg2p⟩ := (E.mem_pairGraph_normal_iff _).mp hN2
  obtain ⟨hst, hsh⟩ := Prod.mk.inj hsp
  obtain ⟨hg1t, hg1h⟩ := Prod.mk.inj hg1p
  obtain ⟨hg2t, hg2h⟩ := Prod.mk.inj hg2p
  have hsL : E.naturalLift s ((e.head.val : ℤ) - e.length.val) ((e.head.val : ℤ) + 1) :=
    E.naturalLift_of_residues ((D.dn_res_a e).trans hst.symm)
      ((D.dn_res_p1 e).trans hsh.symm) (by lia) (by lia)
  have h1L : E.naturalLift g1 ((e.head.val : ℤ) - e.length.val) (e.head.val : ℤ) :=
    E.naturalLift_of_residues ((D.dn_res_a e).trans hg1t.symm)
      ((D.dn_res_p e).trans hg1h.symm) (by lia) (by have := e.length_lt_n; lia)
  have h2L : E.naturalLift g2 (e.head.val : ℤ) ((e.head.val : ℤ) + 1) :=
    E.naturalLift_of_residues ((D.dn_res_p e).trans hg2t.symm)
      ((D.dn_res_p1 e).trans hg2h.symm) (by lia) (by have := D.dn_three_le e he hb; lia)
  have h := E.tri_local_identity_pairs hs hsL h1L h2L ((E.mem_normalEdges_iff _).mp hg1)
    ((E.mem_normalEdges_iff _).mp hg2) Q
  rw [hg1p, hg2p, Finset.insert_comm (e.head, D.area.next e.head)] at h
  exact h

include he hf hcontact heq hb hns hlen in
/-- Both local normal pairs chosen: identical lifted transitive closures. -/
theorem dn_top (Q : Finset (Fin n × Fin n)) (hQ : Q ⊆ D.dnB e f) :
    D.orientMono (D.normalOf
        (insert (e.head, D.area.next e.head) (insert (D.area.next e.head, f.head) Q))) =
      (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).orientMono
        ((D.dnSuccessor e f he hf hne heq hb hns hlen hgap).normalOf
          (insert (e.tail, e.head) (insert (e.head, D.area.next e.head) Q))) := by
  have hLe := D.dn_Le e he
  have hepos := e.length_pos
  have helt := e.length_lt_n
  have hflt := f.length_lt_n
  have hn3 := D.dn_three_le e he hb
  have hN : insert (e.head, D.area.next e.head) (insert (D.area.next e.head, f.head) Q) ⊆
      D.pairGraph.normalEdges := by
    rw [D.dn_N_eq e f he hf hcontact heq hb hns hlen]
    exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hQ)
  have hN' : insert (e.tail, e.head) (insert (e.head, D.area.next e.head) Q) ⊆
      (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).pairGraph.normalEdges := by
    rw [dn_target_normal _ _ _ _ _ _ hcontact]
    exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hQ)
  apply D.orientMono_normalOf_eq_of_transGen _ _ hN hN'
  · rw [dn_target_strict _ _ _ _ _ _ hcontact]
    rintro x y ⟨hmem, h1, h2⟩
    by_cases hIZ : (D.residue x, D.residue y) = (e.head, f.head)
    · obtain ⟨hx, hy⟩ := Prod.mk.inj hIZ
      have hd := D.sub_eq_of_residue_eq (x0 := (e.head.val : ℤ))
        (y0 := (e.head.val : ℤ) + f.length.val) (hx.trans (D.dn_res_p e).symm)
        (hy.trans (D.dn_res_T e f hcontact).symm) h1 h2 (by lia) (by lia)
      have hx1 : D.residue (x + 1) = D.area.next e.head := by rw [D.residue_succ, hx]
      have s1 : D.pairStep (D.dnSt' e f ∪
          insert (e.tail, e.head) (insert (e.head, D.area.next e.head) Q)) x (x + 1) := by
        refine ⟨?_, by lia, by lia⟩
        rw [hx, hx1]
        exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have s2 : D.pairStep (D.dnSt' e f ∪
          insert (e.tail, e.head) (insert (e.head, D.area.next e.head) Q)) (x + 1) y := by
        refine ⟨?_, by lia, by lia⟩
        rw [hx1, hy]
        exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
      exact (Relation.TransGen.single s1).tail s2
    · refine Relation.TransGen.single ⟨?_, h1, h2⟩
      simp only [dnSt', Finset.mem_union, Finset.mem_insert, Finset.mem_erase] at hmem ⊢
      tauto
  · rw [dn_target_strict _ _ _ _ _ _ hcontact]
    rintro x y ⟨hmem, h1, h2⟩
    by_cases hAY : (D.residue x, D.residue y) = (e.tail, D.area.next e.head)
    · obtain ⟨hx, hy⟩ := Prod.mk.inj hAY
      have hd := D.sub_eq_of_residue_eq (x0 := (e.head.val : ℤ) - e.length.val)
        (y0 := (e.head.val : ℤ) + 1) (hx.trans (D.dn_res_a e).symm)
        (hy.trans (D.dn_res_p1 e).symm) h1 h2 (by lia) (by lia)
      have hxL : D.residue (x + e.length.val) = e.head := D.residue_add_length e x hx
      have s1 : D.pairStep (D.pairGraph.strictEdges ∪ insert (e.head, D.area.next e.head)
          (insert (D.area.next e.head, f.head) Q)) x (x + e.length.val) := by
        refine ⟨?_, by lia, by lia⟩
        rw [hx, hxL]
        exact Finset.mem_union_left _ (D.dn_e_pair e he)
      have s2 : D.pairStep (D.pairGraph.strictEdges ∪ insert (e.head, D.area.next e.head)
          (insert (D.area.next e.head, f.head) Q)) (x + e.length.val) y := by
        refine ⟨?_, by lia, by lia⟩
        rw [hxL, hy]
        exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      exact (Relation.TransGen.single s1).tail s2
    · have hAI := D.dn_e_pair e he
      refine Relation.TransGen.single ⟨?_, h1, h2⟩
      simp only [dnSt', Finset.mem_union, Finset.mem_insert, Finset.mem_erase] at hmem ⊢
      rcases hmem with ((h | h | ⟨_, _, h⟩) | h | h | h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact absurd h hAY
      · exact Or.inl h
      · exact Or.inl (h ▸ hAI)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))

include he hf hcontact heq hb hns hlen in
/-- No local normal pair chosen: periodic swap conjugacy with the target. -/
theorem dn_bottom (Q : Finset (Fin n × Fin n)) (hQ : Q ⊆ D.dnB e f) :
    D.orientMono (D.normalOf Q) =
      (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).orientMono
        ((D.dnSuccessor e f he hf hne heq hb hns hlen hgap).normalOf
          (Q.map (swapVertexPair e.head (D.area.next e.head)))) := by
  set D' := D.dnSuccessor e f he hf hne heq hb hns hlen hgap with hD'
  have hQN : Q ⊆ D.pairGraph.normalEdges := hQ.trans (D.dnB_subset e f)
  have hQ' : Q.map (swapVertexPair e.head (D.area.next e.head)) ⊆ D'.pairGraph.normalEdges := by
    rw [hD', dn_target_normal _ _ _ _ _ _ hcontact]
    intro x hx
    refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
    rw [← D.dnB_map_swap e f he hf hcontact heq hb hns hgap]
    exact Finset.map_subset_map.mpr hQ hx
  have hn2 := D.dn_two_le e he hb
  have hi := periodicSwap_involutive n (e.head.val : ℤ) hn2
  have hstep : ∀ x y, D.liftStep (D.normalOf Q) x y ↔
      D'.liftStep (D'.normalOf (Q.map (swapVertexPair e.head (D.area.next e.head))))
        (periodicSwap n (e.head.val : ℤ) x) (periodicSwap n (e.head.val : ℤ) y) := by
    intro x y
    rw [D.liftStep_normalOf_iff Q hQN, D'.liftStep_normalOf_iff _ hQ', hD',
      dn_target_strict _ _ _ _ _ _ hcontact]
    exact D.dn_swap_step e f he hf hcontact heq hb hns hlen hgap Q hQ x y
  have hres : ∀ z w, D.residue z = D.residue w →
      D.residue (periodicSwap n (e.head.val : ℤ) z) =
        D.residue (periodicSwap n (e.head.val : ℤ) w) := by
    intro z w h
    rw [D.dn_res_swap e he hb, D.dn_res_swap e he hb, h]
  have hout : D.liftStep (D.normalOf Q) (e.head.val : ℤ) ((e.head.val : ℤ) + f.length.val) :=
    ⟨f, Finset.mem_union_left _ hf, (D.dn_f_lift e f hcontact).1,
      (D.dn_f_lift e f hcontact).2⟩
  apply D.orientMono_eq_of _ _ (D.normalOf_subset Q) (D'.normalOf_subset _)
  · intro h
    have hZadm : D'.edgeData.Admissible
        (D'.normalOf (Q.map (swapVertexPair e.head (D.area.next e.head)))) := by
      rw [D'.admissible_iff_lift]
      intro z w hzw hzw'
      have hc : Relation.TransGen (D.liftStep (D.normalOf Q))
          (periodicSwap n (e.head.val : ℤ) z) (periodicSwap n (e.head.val : ℤ) w) := by
        refine Relation.TransGen.lift _ (fun a b hab => ?_) _ _ hzw
        change D.liftStep (D.normalOf Q) (periodicSwap n (e.head.val : ℤ) a)
          (periodicSwap n (e.head.val : ℤ) b)
        rw [hstep, hi, hi]
        exact hab
      exact (D.admissible_iff_lift _).mp h _ _ hc (hres z w hzw')
    refine ⟨hZadm, fun h' => ?_⟩
    exact Orientation.hrvMonomial_periodicSwap
      (⟨_, D.normalOf_subset Q, h⟩ : Orientation D)
      (⟨_, D'.normalOf_subset _, h'⟩ : Orientation D') (e.head.val : ℤ) hn2
      ⟨_, hout⟩ hstep
  · intro h'
    rw [D.admissible_iff_lift]
    intro z w hzw hzw'
    have hc : Relation.TransGen
        (D'.liftStep (D'.normalOf (Q.map (swapVertexPair e.head (D.area.next e.head)))))
        (periodicSwap n (e.head.val : ℤ) z) (periodicSwap n (e.head.val : ℤ) w) :=
      Relation.TransGen.lift _ (fun a b hab => (hstep a b).mp hab) _ _ hzw
    exact (D'.admissible_iff_lift _).mp h' _ _ hc (hres z w hzw')


end DN

end Diagram

end VerticalStripLLT.Circular

