import VerticalStripLLT.Circular.DNOrientationBlocks
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.Diagram

open scoped BigOperators Classical

theorem shiftedOrientationExpansion_dnSuccessor {n : ℕ} (D : Diagram n)
    (e f : Edge D.area) (he : e ∈ D.strict) (hf : f ∈ D.strict) (hne : f ≠ e)
    (hcontact : f.tail = e.head)
    (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
    (hb : D.area.area e.head + 1 < n)
    (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
    (hlen : 2 ≤ f.length.val)
    (hgap : D.area.area (D.area.next f.head) < D.area.area f.head) :
    shiftedOrientationExpansion D =
      shiftedOrientationExpansion (D.dnSuccessor e f he hf hne heq hb hns hlen hgap) := by
  classical
  have hIY := D.dn_Y_ne_I e he hb
  have hAI : e.tail ≠ e.head := e.tail_ne_head
  have hIYB : (e.head, D.area.next e.head) ∉ D.dnB e f := fun h =>
    ((D.mem_dnB_iff e f _).mp h).2.1 rfl
  have hYZB : (D.area.next e.head, f.head) ∉ D.dnB e f := fun h =>
    ((D.mem_dnB_iff e f _).mp h).1 rfl
  have hIYB2 : (e.head, D.area.next e.head) ∉ insert (D.area.next e.head, f.head) (D.dnB e f) := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact hIY (Prod.mk.inj h).1.symm
    · exact hIYB h
  have hAIB : (e.tail, e.head) ∉ D.dnB e f := by
    intro h
    have := D.dnB_subset e f h
    rw [normalPairs_eq_sdiff, Finset.mem_sdiff] at this
    exact this.2 (D.dn_e_pair e he)
  have hAIB2 : (e.tail, e.head) ∉ insert (e.head, D.area.next e.head) (D.dnB e f) := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact hAI (Prod.mk.inj h).1
    · exact hAIB h
  have hmm : ∀ t : Finset (Fin n × Fin n),
      (t.map (swapVertexPair e.head (D.area.next e.head))).map
        (swapVertexPair e.head (D.area.next e.head)) = t := by
    intro t
    ext x
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rwa [swapVertexPair_swapVertexPair]
    · intro hx
      exact ⟨_, ⟨x, hx, rfl⟩, swapVertexPair_swapVertexPair _ _ x⟩
  have hbot : ∑ t ∈ (D.dnB e f).powerset, MvPolynomial.C (Polynomial.X ^ t.card) *
        D.orientMono (D.normalOf t) =
      ∑ t ∈ (D.dnB e f).powerset, MvPolynomial.C (Polynomial.X ^ t.card) *
        (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).orientMono
          ((D.dnSuccessor e f he hf hne heq hb hns hlen hgap).normalOf t) := by
    rw [Finset.sum_congr rfl (fun t ht => by
      rw [D.dn_bottom e f he hf hne hcontact heq hb hns hlen hgap t
        (Finset.mem_powerset.mp ht)])]
    apply Finset.sum_nbij' (fun t => t.map (swapVertexPair e.head (D.area.next e.head)))
      (fun t => t.map (swapVertexPair e.head (D.area.next e.head)))
    · intro t ht
      rw [Finset.mem_powerset] at ht ⊢
      rw [← D.dnB_map_swap e f he hf hcontact heq hb hns hgap]
      exact Finset.map_subset_map.mpr ht
    · intro t ht
      rw [Finset.mem_powerset] at ht ⊢
      rw [← D.dnB_map_swap e f he hf hcontact heq hb hns hgap]
      exact Finset.map_subset_map.mpr ht
    · intro t _
      exact hmm t
    · intro t _
      exact hmm t
    · intro t _
      rw [Finset.card_map]
  have htop : ∑ t ∈ (D.dnB e f).powerset, MvPolynomial.C (Polynomial.X ^ t.card) *
        D.orientMono (D.normalOf (insert (e.head, D.area.next e.head)
          (insert (D.area.next e.head, f.head) t))) =
      ∑ t ∈ (D.dnB e f).powerset, MvPolynomial.C (Polynomial.X ^ t.card) *
        (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).orientMono
          ((D.dnSuccessor e f he hf hne heq hb hns hlen hgap).normalOf
            (insert (e.tail, e.head) (insert (e.head, D.area.next e.head) t))) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [D.dn_top e f he hf hne hcontact heq hb hns hlen hgap t (Finset.mem_powerset.mp ht)]
  rw [D.shiftedOrientationExpansion_eq_pairSum,
    (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).shiftedOrientationExpansion_eq_pairSum,
    D.dn_N_eq e f he hf hcontact heq hb hns hlen,
    D.dn_target_normal e f he hf hne hcontact heq hb hns hlen hgap,
    Finset.sum_powerset_insert hIYB2, Finset.sum_powerset_insert hYZB,
    Finset.sum_powerset_insert hYZB, Finset.sum_powerset_insert hAIB2,
    Finset.sum_powerset_insert hIYB, Finset.sum_powerset_insert hIYB]
  simp only [← Finset.sum_add_distrib]
  calc _ = ∑ t ∈ (D.dnB e f).powerset, MvPolynomial.C (Polynomial.X + 1) *
        (MvPolynomial.C (Polynomial.X ^ t.card) * D.orientMono (D.normalOf t) +
          MvPolynomial.C Polynomial.X * (MvPolynomial.C (Polynomial.X ^ t.card) *
            D.orientMono (D.normalOf (insert (e.head, D.area.next e.head)
              (insert (D.area.next e.head, f.head) t))))) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mem_powerset] at ht
        have h1 : (D.area.next e.head, f.head) ∉ t := fun h => hYZB (ht h)
        have h2 : (e.head, D.area.next e.head) ∉ t := fun h => hIYB (ht h)
        have h3 : (e.head, D.area.next e.head) ∉ insert (D.area.next e.head, f.head) t := by
          rw [Finset.mem_insert]
          rintro (h | h)
          · exact hIY (Prod.mk.inj h).1.symm
          · exact h2 h
        have hid := D.dn_source_local e f he hf hcontact heq hns hlen t
        rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
          Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h1]
        simp only [map_pow, map_add, map_one, map_mul, pow_succ]
        linear_combination (MvPolynomial.C Polynomial.X ^ t.card * MvPolynomial.C Polynomial.X) *
          hid
    _ = MvPolynomial.C (Polynomial.X + 1) *
        (∑ t ∈ (D.dnB e f).powerset, MvPolynomial.C (Polynomial.X ^ t.card) *
          D.orientMono (D.normalOf t) + MvPolynomial.C Polynomial.X *
          ∑ t ∈ (D.dnB e f).powerset, MvPolynomial.C (Polynomial.X ^ t.card) *
            D.orientMono (D.normalOf (insert (e.head, D.area.next e.head)
              (insert (D.area.next e.head, f.head) t)))) := by
        simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    _ = MvPolynomial.C (Polynomial.X + 1) *
        (∑ t ∈ (D.dnB e f).powerset, MvPolynomial.C (Polynomial.X ^ t.card) *
          (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).orientMono
            ((D.dnSuccessor e f he hf hne heq hb hns hlen hgap).normalOf t) +
          MvPolynomial.C Polynomial.X *
          ∑ t ∈ (D.dnB e f).powerset, MvPolynomial.C (Polynomial.X ^ t.card) *
            (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).orientMono
              ((D.dnSuccessor e f he hf hne heq hb hns hlen hgap).normalOf
                (insert (e.tail, e.head) (insert (e.head, D.area.next e.head) t)))) := by
        rw [hbot, htop]
    _ = ∑ t ∈ (D.dnB e f).powerset, MvPolynomial.C (Polynomial.X + 1) *
        (MvPolynomial.C (Polynomial.X ^ t.card) *
          (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).orientMono
            ((D.dnSuccessor e f he hf hne heq hb hns hlen hgap).normalOf t) +
          MvPolynomial.C Polynomial.X * (MvPolynomial.C (Polynomial.X ^ t.card) *
            (D.dnSuccessor e f he hf hne heq hb hns hlen hgap).orientMono
              ((D.dnSuccessor e f he hf hne heq hb hns hlen hgap).normalOf
                (insert (e.tail, e.head) (insert (e.head, D.area.next e.head) t))))) := by
        simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mem_powerset] at ht
        have h1 : (e.head, D.area.next e.head) ∉ t := fun h => hIYB (ht h)
        have h2 : (e.tail, e.head) ∉ t := fun h => hAIB (ht h)
        have h3 : (e.tail, e.head) ∉ insert (e.head, D.area.next e.head) t := by
          rw [Finset.mem_insert]
          rintro (h | h)
          · exact hAI (Prod.mk.inj h).1
          · exact h2 h
        have hid := D.dn_target_local e f he hf hne hcontact heq hb hns hlen hgap t
        rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
          Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h1]
        simp only [map_pow, map_add, map_one, map_mul, pow_succ]
        linear_combination (-(MvPolynomial.C Polynomial.X ^ t.card * MvPolynomial.C Polynomial.X)) *
          hid

end VerticalStripLLT.Circular.Diagram
