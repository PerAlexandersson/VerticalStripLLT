import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith

open scoped BigOperators Classical

namespace VerticalStripLLT.Circular.ChainSingletonComb

variable {R : Type*} [CommRing R]

theorem sum_powerset_pow {α : Type*} (s : Finset α) (q : R) :
    ∑ A ∈ s.powerset, q ^ A.card = (1 + q) ^ s.card := by
  have h := Finset.sum_pow_mul_eq_add_pow q 1 s
  simp only [one_pow, mul_one] at h
  rw [h, add_comm]

theorem sum_powerset_filter_forall {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p]
    (f : Finset α → R) :
    ∑ A ∈ s.powerset, (if ∀ x ∈ A, p x then f A else 0) =
      ∑ A ∈ (s.filter p).powerset, f A := by
  rw [← Finset.sum_filter]
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff]
  constructor
  · rintro ⟨h1, h2⟩ x hx
    exact ⟨h1 hx, h2 x hx⟩
  · intro h
    exact ⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩

/-- Nonempty subsets decompose by their least element. -/
theorem sum_nonempty_powerset_by_min {k : ℕ} (I : Finset (Fin (k + 1)))
    (F : Finset (Fin (k + 1)) → R) :
    ∑ V ∈ I.powerset, (if V.Nonempty then F V else 0) =
      ∑ h ∈ I, ∑ W ∈ (I.filter (h < ·)).powerset, F (insert h W) := by
  rw [← Finset.sum_filter, Finset.sum_sigma']
  symm
  apply Finset.sum_bij (fun p _ => insert p.1 p.2)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hp
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset hp.1 (hp.2.trans (Finset.filter_subset _ _)),
      Finset.insert_nonempty _ _⟩
  · intro p hp p' hp' h
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hp hp'
    have hmin : ∀ (x : Fin (k + 1)) (W : Finset (Fin (k + 1))), W ⊆ I.filter (x < ·) →
        ∀ y ∈ insert x W, x ≤ y := by
      intro x W hW y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact le_rfl
      · exact le_of_lt (Finset.mem_filter.mp (hW hy)).2
    have h1 : p.1 = p'.1 := by
      apply le_antisymm
      · exact hmin p.1 p.2 hp.2 p'.1 (h ▸ Finset.mem_insert_self _ _)
      · exact hmin p'.1 p'.2 hp'.2 p.1 (h.symm ▸ Finset.mem_insert_self _ _)
    have hn : ∀ (x : Fin (k + 1)) (W : Finset (Fin (k + 1))), W ⊆ I.filter (x < ·) →
        x ∉ W := fun x W hW hx => lt_irrefl x (Finset.mem_filter.mp (hW hx)).2
    have h2 : p.2 = p'.2 := by
      have e1 := Finset.erase_insert (hn _ _ hp.2)
      have e2 := Finset.erase_insert (hn _ _ hp'.2)
      rw [← e1, ← e2, h, h1]
    rcases p with ⟨a, b⟩
    rcases p' with ⟨a', b'⟩
    simp only at h1 h2
    subst h1; subst h2; rfl
  · intro V hV
    simp only [Finset.mem_filter, Finset.mem_powerset] at hV
    refine ⟨⟨V.min' hV.2, V.erase (V.min' hV.2)⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_powerset]
      refine ⟨hV.1 (Finset.min'_mem _ _), ?_⟩
      intro x hx
      rw [Finset.mem_erase] at hx
      rw [Finset.mem_filter]
      exact ⟨hV.1 hx.2, lt_of_le_of_ne (Finset.min'_le _ _ hx.2) (Ne.symm hx.1)⟩
    · exact Finset.insert_erase (Finset.min'_mem V hV.2)
  · intro p hp
    rfl

/-- The counting identity: above and below a selected incoming position. -/
theorem card_below_add_card_above {k : ℕ} (O I : Finset (Fin (k + 1)))
    (hOI : ∀ i : Fin k, i.succ ∈ I ↔ i.castSucc ∈ O) (h : Fin (k + 1)) :
    (O.filter (· < h)).card + (I.filter (h < ·)).card = (O.erase (Fin.last k)).card := by
  have habove : (I.filter (h < ·)).card = ((O.erase (Fin.last k)).filter (h ≤ ·)).card := by
    apply Finset.card_bij (fun x _ => (⟨x.val - 1, by lia⟩ : Fin (k + 1)))
    · intro x hx
      simp only [Finset.mem_filter] at hx
      have hx0 : 0 < x.val := lt_of_le_of_lt (Nat.zero_le _) hx.2
      have hi := (hOI ⟨x.val - 1, by lia⟩).mp (by
        convert hx.1 using 1
        ext; simp; lia)
      simp only [Finset.mem_filter, Finset.mem_erase]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro heq
        have := congrArg Fin.val heq
        simp at this
        lia
      · convert hi using 1
        exact Fin.ext rfl
      · rw [Fin.le_def]
        have := Fin.lt_def.mp hx.2
        simp
        lia
    · intro x hx y hy hxy
      simp only [Finset.mem_filter] at hx hy
      have h1 := Fin.lt_def.mp hx.2
      have h2 := Fin.lt_def.mp hy.2
      have := congrArg Fin.val hxy
      simp at this
      ext
      lia
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_erase] at hy
      have hyk : y.val < k := by
        have hy1 := hy.1.1
        have : y.val ≠ k := fun h' => hy1 (Fin.ext (by simpa using h'))
        lia
      refine ⟨⟨y.val + 1, by lia⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · have := (hOI ⟨y.val, hyk⟩).mpr (by
            convert hy.1.2 using 1
            exact Fin.ext rfl)
          convert this using 1
          exact Fin.ext rfl
        · rw [Fin.lt_def]
          have := Fin.le_def.mp hy.2
          simp
          lia
      · ext
        simp
  rw [habove]
  have hbelow : O.filter (· < h) = (O.erase (Fin.last k)).filter (· < h) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hx, hxh⟩
      refine ⟨⟨?_, hx⟩, hxh⟩
      intro heq
      subst heq
      exact absurd (Fin.le_last h) (not_le.mpr hxh)
    · rintro ⟨⟨_, hx⟩, hxh⟩
      exact ⟨hx, hxh⟩
  rw [hbelow, ← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h' | h')
      · exact h'.1
      · exact h'.1
    · intro hx
      by_cases hxh : x < h
      · exact Or.inl ⟨hx, hxh⟩
      · exact Or.inr ⟨hx, not_lt.mp hxh⟩
  · rw [Finset.disjoint_filter]
    intro x _ h1 h2
    exact absurd h2 (not_le.mpr h1)

/-- The finite selection sum for a chain and one isolated vertex. -/
theorem selection_sum {k : ℕ} (O I : Finset (Fin (k + 1)))
    (hOI : ∀ i : Fin k, i.succ ∈ I ↔ i.castSucc ∈ O) (q a b : R) :
    ∑ U ∈ O.powerset, ∑ V ∈ I.powerset, q ^ (U.card + V.card) *
      (if ∃ j ∈ U, ∃ h ∈ V, h ≤ j then 0 else
        if V.Nonempty ∨ Fin.last k ∈ U then a else b) =
    (1 + q) ^ (O.erase (Fin.last k)).card *
      (b + (((if (0 : Fin (k + 1)) ∈ I then 1 else 0) + (O.erase (Fin.last k)).card +
        (if Fin.last k ∈ O then 1 else 0) : ℕ) : R) * q * a) := by
  set M := (O.erase (Fin.last k)).card with hM
  rw [Finset.sum_comm]
  -- split off V = ∅
  have hsplit : ∀ V ∈ I.powerset,
      (∑ U ∈ O.powerset, q ^ (U.card + V.card) *
        (if ∃ j ∈ U, ∃ h ∈ V, h ≤ j then 0 else
          if V.Nonempty ∨ Fin.last k ∈ U then a else b)) =
      (if V.Nonempty then
        ∑ U ∈ O.powerset, q ^ (U.card + V.card) *
          (if ∃ j ∈ U, ∃ h ∈ V, h ≤ j then 0 else a) else 0) +
      (if V = ∅ then ∑ U ∈ O.powerset, q ^ U.card *
          (if Fin.last k ∈ U then a else b) else 0) := by
    intro V _
    by_cases hV : V.Nonempty
    · have hV' : V ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hV
      simp only [hV, hV', ite_true, ite_false, true_or, add_zero]
    · have hV' : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hV
      subst hV'
      simp
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    sum_nonempty_powerset_by_min, Finset.sum_ite_eq' I.powerset ∅]
  simp only [Finset.empty_mem_powerset, ite_true]
  -- the V = ∅ part
  have hempty : ∑ U ∈ O.powerset, q ^ U.card * (if Fin.last k ∈ U then a else b) =
      (1 + q) ^ M * (b + ((if Fin.last k ∈ O then 1 else 0 : ℕ) : R) * q * a) := by
    by_cases hl : Fin.last k ∈ O
    · rw [← Finset.insert_erase hl, Finset.sum_powerset_insert (Finset.notMem_erase _ _)]
      have h1 : ∀ U ∈ (O.erase (Fin.last k)).powerset, q ^ U.card *
          (if Fin.last k ∈ U then a else b) = q ^ U.card * b := by
        intro U hU
        have : Fin.last k ∉ U := fun h =>
          Finset.notMem_erase (Fin.last k) O (Finset.mem_powerset.mp hU h)
        simp [this]
      have h2 : ∀ U ∈ (O.erase (Fin.last k)).powerset,
          q ^ (insert (Fin.last k) U).card *
            (if Fin.last k ∈ insert (Fin.last k) U then a else b) = q ^ U.card * (q * a) := by
        intro U hU
        have : Fin.last k ∉ U := fun h =>
          Finset.notMem_erase (Fin.last k) O (Finset.mem_powerset.mp hU h)
        rw [Finset.card_insert_of_notMem this, ite_eq_left (Finset.mem_insert_self _ _)]
        ring
      rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.sum_mul, ← Finset.sum_mul,
        sum_powerset_pow, ite_eq_left (Finset.mem_insert_self _ _)]
      simp only [hM]
      push_cast
      ring
    · have he : O.erase (Fin.last k) = O := Finset.erase_eq_of_notMem hl
      have h1 : ∀ U ∈ O.powerset, q ^ U.card *
          (if Fin.last k ∈ U then a else b) = q ^ U.card * b := by
        intro U hU
        have : Fin.last k ∉ U := fun h => hl (Finset.mem_powerset.mp hU h)
        simp [this]
      rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, sum_powerset_pow, ite_eq_right hl, hM, he]
      push_cast
      ring
  -- the nonempty part
  have hne : ∀ h ∈ I, ∑ W ∈ (I.filter (h < ·)).powerset,
      ∑ U ∈ O.powerset, q ^ (U.card + (insert h W).card) *
        (if ∃ j ∈ U, ∃ h' ∈ insert h W, h' ≤ j then 0 else a) =
        (1 + q) ^ M * (q * a) := by
    intro h _
    have hW : ∀ W ∈ (I.filter (h < ·)).powerset,
        ∑ U ∈ O.powerset, q ^ (U.card + (insert h W).card) *
          (if ∃ j ∈ U, ∃ h' ∈ insert h W, h' ≤ j then 0 else a) =
        q ^ W.card * ((1 + q) ^ (O.filter (· < h)).card * (q * a)) := by
      intro W hWm
      have hWsub := Finset.mem_powerset.mp hWm
      have hhW : h ∉ W := fun hh => lt_irrefl h (Finset.mem_filter.mp (hWsub hh)).2
      have hcond : ∀ U : Finset (Fin (k + 1)),
          (∃ j ∈ U, ∃ h' ∈ insert h W, h' ≤ j) ↔ ¬ ∀ j ∈ U, j < h := by
        intro U
        constructor
        · rintro ⟨j, hj, h', hh', hle⟩ hall
          have hjh := hall j hj
          rcases Finset.mem_insert.mp hh' with rfl | hh'
          · exact absurd hle (not_le.mpr hjh)
          · have := (Finset.mem_filter.mp (hWsub hh')).2
            exact absurd (lt_of_lt_of_le this hle) (not_lt.mpr (le_of_lt hjh))
        · intro hn
          push Not at hn
          obtain ⟨j, hj, hle⟩ := hn
          exact ⟨j, hj, h, Finset.mem_insert_self _ _, hle⟩
      have hterm : ∀ U ∈ O.powerset, q ^ (U.card + (insert h W).card) *
          (if ∃ j ∈ U, ∃ h' ∈ insert h W, h' ≤ j then 0 else a) =
          (if ∀ j ∈ U, j < h then q ^ U.card * (q ^ W.card * (q * a)) else 0) := by
        intro U _
        rw [Finset.card_insert_of_notMem hhW]
        by_cases hU : ∀ j ∈ U, j < h
        · rw [ite_eq_right (fun hc => (hcond U).mp hc hU), ite_eq_left hU]
          ring
        · rw [ite_eq_left ((hcond U).mpr hU), ite_eq_right hU, mul_zero]
      rw [Finset.sum_congr rfl hterm]
      rw [show (∑ x ∈ O.powerset,
          if ∀ j ∈ x, j < h then q ^ x.card * (q ^ W.card * (q * a)) else 0) =
          ∑ x ∈ (O.filter (· < h)).powerset,
            q ^ x.card * (q ^ W.card * (q * a)) from by
        convert sum_powerset_filter_forall O (· < h)
          (fun x => q ^ x.card * (q ^ W.card * (q * a)))]
      rw [← Finset.sum_mul, sum_powerset_pow]
      ring
    rw [Finset.sum_congr rfl hW, ← Finset.sum_mul, sum_powerset_pow]
    rw [mul_left_comm, ← mul_assoc, ← pow_add, card_below_add_card_above O I hOI h]
  rw [Finset.sum_congr rfl hne, Finset.sum_const, hempty]
  -- card of I
  have hI : I.card = (if (0 : Fin (k + 1)) ∈ I then 1 else 0) + M := by
    have h0 := card_below_add_card_above O I hOI 0
    have hz : O.filter (· < (0 : Fin (k + 1))) = ∅ := by
      ext x
      simp
    rw [hz, Finset.card_empty, zero_add] at h0
    rw [hM, ← h0, ← Finset.card_filter_add_card_filter_not (fun x => 0 < x) (s := I)]
    have hneg : I.filter (fun x => ¬ (0 : Fin (k + 1)) < x) = I.filter (fun x => x = 0) := by
      apply Finset.filter_congr
      intro x _
      simp [Fin.pos_iff_ne_zero]
    rw [hneg, Finset.filter_eq' I 0]
    split_ifs <;> simp [add_comm]
  rw [nsmul_eq_mul, hI]
  push_cast
  ring

end VerticalStripLLT.Circular.ChainSingletonComb
