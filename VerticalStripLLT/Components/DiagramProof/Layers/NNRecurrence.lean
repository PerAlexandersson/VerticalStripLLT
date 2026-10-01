import VerticalStripLLT.Components.DiagramProof.Layers.LocalSplit

/-!
# The NN recurrence on full edge layers

At an NN contact the strict root `xt` has the adjacent shorts `q = xy` and
`r = yt`, with `y = x + 1`. The target shortens the root to `yt`, which becomes
strict. Split the states by the two local shorts. The diamond at `x < y < t`,
the swap of `x, y` on the states with neither short, and closure equality on the
states with both give, for every fixed colour of the greatest vertex,

    X(layer_(s+1) L) = X(layer_(s+1) R) + X(layer_s R),   X = K, E.

The target loses the natural edge `xt`, so its natural area is smaller.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-! ### The algebra of the split -/

section Algebra

variable {α M : Type*} [DecidableEq α] [AddCommGroup M]

theorem card_insert_of_mem_powerset {X Q : Finset α} {q : α} (hq : q ∉ X)
    (hQ : Q ∈ X.powerset) : (insert q Q).card = Q.card + 1 :=
  Finset.card_insert_of_notMem fun h => hq (Finset.mem_powerset.mp hQ h)

/-- The layer bookkeeping of the NN recurrence. -/
theorem nn_sum_algebra {X : Finset α} {q r : α} (hq : q ∉ X) (hr : r ∉ X) (hqr : q ≠ r)
    (c s : ℕ) (f g : Finset α → M) (σ : Finset α → Finset α)
    (hσ : ∀ φ : Finset α → M, ∑ P ∈ X.powerset, φ P = ∑ Q ∈ X.powerset, φ (σ Q))
    (hσcard : ∀ Q ∈ X.powerset, (σ Q).card = Q.card)
    (hdia : ∀ Q ∈ X.powerset,
      f (insert q Q) + f (insert r Q) = f Q + f (insert q (insert r Q)))
    (h0 : ∀ Q ∈ X.powerset, g (σ Q) = f Q)
    (h1 : ∀ Q ∈ X.powerset, g (insert q Q) = f (insert q (insert r Q))) :
    ∑ Q ∈ X.powerset,
        ((if c + Q.card = s + 1 then f Q else 0) +
          (if c + (insert q Q).card = s + 1 then f (insert q Q) else 0) +
          (if c + (insert r Q).card = s + 1 then f (insert r Q) else 0) +
          (if c + (insert q (insert r Q)).card = s + 1 then f (insert q (insert r Q)) else 0)) =
      ∑ P ∈ X.powerset,
          ((if c + P.card = s + 1 then g P else 0) +
            (if c + (insert q P).card = s + 1 then g (insert q P) else 0)) +
        ∑ P ∈ X.powerset,
          ((if c + P.card = s then g P else 0) +
            (if c + (insert q P).card = s then g (insert q P) else 0)) := by
  have hrq : r ∉ insert q X := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hqr.symm, hr⟩
  rw [← Finset.sum_add_distrib]
  -- Move the `g P` terms through the relabelling.
  have hsplit : ∀ P ∈ X.powerset,
      (if c + P.card = s + 1 then g P else 0) +
          (if c + (insert q P).card = s + 1 then g (insert q P) else 0) +
        ((if c + P.card = s then g P else 0) +
          (if c + (insert q P).card = s then g (insert q P) else 0)) =
      ((if c + P.card = s + 1 then g P else 0) + (if c + P.card = s then g P else 0)) +
        ((if c + P.card = s then g (insert q P) else 0) +
          (if c + P.card + 1 = s then g (insert q P) else 0)) := by
    intro P hP
    rw [card_insert_of_mem_powerset hq hP]
    have e1 : c + (P.card + 1) = s + 1 ↔ c + P.card = s := by
      constructor <;> intro <;> lia
    have e2 : c + (P.card + 1) = s ↔ c + P.card + 1 = s := by
      constructor <;> intro <;> lia
    simp only [e1, e2]
    abel
  rw [Finset.sum_congr rfl hsplit]
  conv_rhs => rw [Finset.sum_add_distrib,
    hσ (fun P => (if c + P.card = s + 1 then g P else 0) + (if c + P.card = s then g P else 0)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have hcqr : (insert q (insert r Q)).card = Q.card + 1 + 1 := by
    rw [Finset.card_insert_of_notMem, card_insert_of_mem_powerset hr hQ]
    intro hm
    rcases Finset.mem_insert.mp hm with he | hm
    · exact hqr he
    · exact hq (Finset.mem_powerset.mp hQ hm)
  rw [hσcard Q hQ, h0 Q hQ, h1 Q hQ, hcqr]
  simp only [card_insert_of_mem_powerset hq hQ, card_insert_of_mem_powerset hr hQ]
  have e1 : c + (Q.card + 1) = s + 1 ↔ c + Q.card = s := by
    constructor <;> intro <;> lia
  have e3 : c + (Q.card + 1 + 1) = s + 1 ↔ c + Q.card + 1 = s := by
    constructor <;> intro <;> lia
  simp only [e1, e3]
  by_cases hc : c + Q.card = s
  · have hne : ¬ s = s + 1 := by lia
    have hne' : ¬ s + 1 = s := by lia
    simp only [hc, hne, hne', ite_true, ite_false, zero_add, add_zero]
    exact hdia Q hQ
  · simp only [hc, ite_false]
    abel

end Algebra

/-! ### The contact and its target -/

variable {k : ℕ} {D : Diagram (k + 1)} (hD : Forward D)

/-- An eligible NN contact at the strict root `xt`, with `y = x + 1`. -/
structure NNContact (D : Diagram (k + 1)) (x y t : Fin (k + 1)) : Prop where
  succ : y.val = x.val + 1
  yt : y < t
  root : strictRel D x t
  gap : ∀ p q, naturalRel D p q → t < q → y < p
  boundary : ∀ p, p < x → (naturalRel D p x ↔ naturalRel D p y)
  xy : naturalRel D x y
  tailx : ∀ b, strictRel D x b → b = t
  taily : ∀ b, ¬ strictRel D y b
  headx : ∀ a, ¬ strictRel D a x
  heady : ∀ a, ¬ strictRel D a y

namespace NNContact

variable {x y t : Fin (k + 1)} (h : NNContact D x y t)

include h

theorem xy_lt : x < y := by
  rw [Fin.lt_def, h.succ]
  lia

theorem ne_xy : x ≠ y := h.xy_lt.ne

include hD in
theorem nat_yt : naturalRel D y t :=
  (naturalRel_interval hD (naturalRel_of_strictRel h.root) h.xy_lt h.yt).2

theorem normal_xy : (x, y) ∈ normalPairs D :=
  mem_normalPairs.mpr ⟨h.xy, h.heady x⟩

include hD in
theorem normal_yt : (y, t) ∈ normalPairs D :=
  mem_normalPairs.mpr ⟨h.nat_yt hD, h.taily t⟩

theorem pair_ne : ((x, y) : Fin (k + 1) × Fin (k + 1)) ≠ (y, t) := by
  intro he
  exact h.ne_xy (Prod.mk.inj he).1

/-- Every strict pair other than the root avoids `x` and `y`. -/
theorem strict_cases {a b : Fin (k + 1)} (hab : strictRel D a b) :
    (a = x ∧ b = t) ∨ (a ≠ x ∧ a ≠ y ∧ b ≠ x ∧ b ≠ y) := by
  by_cases ha : a = x
  · subst ha
    exact Or.inl ⟨rfl, h.tailx b hab⟩
  · refine Or.inr ⟨ha, ?_, ?_, ?_⟩
    · rintro rfl
      exact h.taily b hab
    · rintro rfl
      exact h.headx a hab
    · rintro rfl
      exact h.heady a hab

include hD in
theorem yt_maximal : MaximalPair (fun a b => naturalRel D a b ∧ ¬ (a = x ∧ b = t)) y t := by
  refine ⟨⟨h.nat_yt hD, fun he => h.ne_xy he.1.symm⟩, ?_⟩
  rintro p q ⟨hpq, hne⟩ hpy htq
  have hq : q = t := by
    by_contra hqt
    have := h.gap p q hpq (lt_of_le_of_ne htq (Ne.symm hqt))
    exact absurd hpy (not_le_of_gt this)
  subst hq
  refine ⟨?_, rfl⟩
  by_cases hpx : p ≤ x
  · obtain ⟨rfl, -⟩ := strictRel_maximal hD h.root hpq hpx le_rfl
    exact (hne ⟨rfl, rfl⟩).elim
  · apply le_antisymm hpy
    rw [Fin.le_def, h.succ]
    have : x.val < p.val := lt_of_not_ge hpx
    lia

end NNContact

variable {x y t : Fin (k + 1)} (h : NNContact D x y t)

/-- The NN target: the root `xt` is shortened to the strict pair `yt`. -/
def nnTarget : Diagram (k + 1) :=
  ofRelations (fun a b => naturalRel D a b ∧ ¬ (a = x ∧ b = t))
    (fun a b => (strictRel D a b ∧ ¬ (a = x ∧ b = t)) ∨ (a = y ∧ b = t))
    ((ordinaryRelation_naturalRel hD).removeMaximal _
      (by rintro _ _ ⟨rfl, rfl⟩; exact maximalPair_of_strictRel hD h.root))
    (by
      rintro a b (⟨hs, hne⟩ | ⟨rfl, rfl⟩)
      · exact (maximalPair_of_strictRel hD hs).of_le (fun _ _ h' => h'.1)
          ⟨naturalRel_of_strictRel hs, hne⟩
      · exact h.yt_maximal hD)
    D.area.positive

theorem nnTarget_forward : Forward (nnTarget hD h) := ofRelations_forward _ _ _ _ _

theorem nnTarget_naturalRel (a b : Fin (k + 1)) :
    naturalRel (nnTarget hD h) a b ↔ naturalRel D a b ∧ ¬ (a = x ∧ b = t) :=
  ofRelations_naturalRel ..

theorem nnTarget_strictRel (a b : Fin (k + 1)) :
    strictRel (nnTarget hD h) a b ↔
      (strictRel D a b ∧ ¬ (a = x ∧ b = t)) ∨ (a = y ∧ b = t) :=
  ofRelations_strictRel ..

/-- The swap of the contact vertices. -/
abbrev nnSwap (x y : Fin (k + 1)) : Equiv.Perm (Fin (k + 1)) := Equiv.swap x y

theorem nnSwap_involutive (v : Fin (k + 1)) : nnSwap x y (nnSwap x y v) = v :=
  Equiv.swap_apply_self x y v

namespace NNContact

include h

theorem t_ne_x : t ≠ x := (h.xy_lt.trans h.yt).ne'

theorem t_ne_y : t ≠ y := h.yt.ne'

theorem swap_t : nnSwap x y t = t := Equiv.swap_apply_of_ne_of_ne h.t_ne_x h.t_ne_y

theorem swap_last : nnSwap x y (Fin.last k) = Fin.last k := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact ((h.xy_lt.trans h.yt).trans_le (Fin.le_last t)).ne'
  · exact (h.yt.trans_le (Fin.le_last t)).ne'

omit h in
theorem swap_eq_x {a : Fin (k + 1)} : nnSwap x y a = x ↔ a = y := by
  rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

omit h in
theorem swap_eq_y {a : Fin (k + 1)} : nnSwap x y a = y ↔ a = x := by
  rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]

theorem swap_eq_t {a : Fin (k + 1)} : nnSwap x y a = t ↔ a = t := by
  rw [Equiv.swap_apply_eq_iff, h.swap_t]

omit h in
theorem swap_fix {a : Fin (k + 1)} (hx : a ≠ x) (hy : a ≠ y) : nnSwap x y a = a :=
  Equiv.swap_apply_of_ne_of_ne hx hy

omit h in
/-- A vertex whose image avoids the swapped pair is fixed. -/
theorem swap_back {a : Fin (k + 1)} (hx : nnSwap x y a ≠ x) (hy : nnSwap x y a ≠ y) :
    nnSwap x y a = a := by
  have := swap_fix hx hy
  rw [nnSwap_involutive] at this
  exact this.symm

omit h in
/-- Swapping `x` and `x + 1` preserves the order of sinks when `x` is not a sink. -/
theorem swap_sinkOrder {D : Diagram (k + 1)} {θ : Orientation D} {x y t : Fin (k + 1)}
    (hsucc : y.val = x.val + 1) (hxt : D.edgeData.selected θ.val x t) (u w : Fin (k + 1))
    (hu : ∀ z, ¬ D.edgeData.selected θ.val u z) (hw : ∀ z, ¬ D.edgeData.selected θ.val w z)
    (huw : u ≤ w) : nnSwap x y u ≤ nnSwap x y w := by
  have hux : u ≠ x := fun he => hu t (he ▸ hxt)
  have hwx : w ≠ x := fun he => hw t (he ▸ hxt)
  have hxy : x < y := by rw [Fin.lt_def, hsucc]; lia
  by_cases huy : u = y
  · rw [huy, Equiv.swap_apply_right]
    by_cases hwy : w = y
    · rw [hwy, Equiv.swap_apply_right]
    · rw [swap_fix hwx hwy]
      exact hxy.le.trans (huy ▸ huw)
  · rw [swap_fix hux huy]
    by_cases hwy : w = y
    · rw [hwy, Equiv.swap_apply_right, Fin.le_def]
      have h1 : u.val ≤ w.val := huw
      rw [hwy] at h1
      have h2 : u.val ≠ y.val := fun he => huy (Fin.ext he)
      have h3 : u.val ≠ x.val := fun he => hux (Fin.ext he)
      lia
    · rw [swap_fix hwx hwy]
      exact huw

include hD

/-- Strict pairs correspond under the swap. -/
theorem strictRel_swap (a b : Fin (k + 1)) :
    strictRel (nnTarget hD h) (nnSwap x y a) (nnSwap x y b) ↔ strictRel D a b := by
  rw [nnTarget_strictRel]
  constructor
  · rintro (⟨hs, hne⟩ | ⟨ha, hb⟩)
    · rcases h.strict_cases hs with ⟨ha', hb'⟩ | ⟨h1, h2, h3, h4⟩
      · exact (hne ⟨ha', hb'⟩).elim
      · rw [swap_back h1 h2, swap_back h3 h4] at hs
        exact hs
    · rw [swap_eq_y] at ha
      rw [h.swap_eq_t] at hb
      subst ha hb
      exact h.root
  · intro hs
    rcases h.strict_cases hs with ⟨rfl, rfl⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inr ⟨Equiv.swap_apply_left _ _, h.swap_t⟩
    · rw [swap_fix h1 h2, swap_fix h3 h4]
      exact Or.inl ⟨hs, fun he => h1 he.1⟩

theorem strictPairs_target :
    strictPairs (nnTarget hD h) = relabelPairs (nnSwap x y) (strictPairs D) := by
  ext ⟨a', b'⟩
  obtain ⟨a, rfl⟩ := (nnSwap x y).surjective a'
  obtain ⟨b, rfl⟩ := (nnSwap x y).surjective b'
  rw [mem_relabelPairs, mem_strictPairs, mem_strictPairs]
  exact h.strictRel_swap hD a b

theorem card_strictPairs_target :
    (strictPairs (nnTarget hD h)).card = (strictPairs D).card := by
  rw [h.strictPairs_target hD, card_relabelPairs]

/-- The common exterior normal pairs. -/
abbrev exterior (D : Diagram (k + 1)) (x y t : Fin (k + 1)) : Finset (Fin (k + 1) × Fin (k + 1)) :=
  ((normalPairs D).erase (x, y)).erase (y, t)

omit h hD in
theorem mem_exterior {p : Fin (k + 1) × Fin (k + 1)} :
    p ∈ exterior D x y t ↔ (naturalRel D p.1 p.2 ∧ ¬ strictRel D p.1 p.2) ∧
      p ≠ (x, y) ∧ p ≠ (y, t) := by
  simp only [Finset.mem_erase, mem_normalPairs]
  tauto

theorem normalPairs_target_xy : (x, y) ∈ normalPairs (nnTarget hD h) := by
  rw [mem_normalPairs, nnTarget_naturalRel, nnTarget_strictRel]
  refine ⟨⟨h.xy, fun he => h.t_ne_y he.2.symm⟩, ?_⟩
  rintro (⟨hs, -⟩ | ⟨he, -⟩)
  · exact h.heady x hs
  · exact h.ne_xy he

theorem normalPairs_target_erase :
    (normalPairs (nnTarget hD h)).erase (x, y) = exterior D x y t := by
  ext ⟨a, b⟩
  rw [mem_exterior, Finset.mem_erase, mem_normalPairs, nnTarget_naturalRel,
    nnTarget_strictRel]
  simp only [ne_eq, Prod.mk.injEq]
  have hroot := h.root
  constructor
  · rintro ⟨hxy, ⟨hn, hxt⟩, hns⟩
    refine ⟨⟨hn, fun hs => hns (Or.inl ⟨hs, hxt⟩)⟩, hxy, fun he => hns (Or.inr he)⟩
  · rintro ⟨⟨hn, hns⟩, hxy, hyt⟩
    refine ⟨hxy, ⟨hn, ?_⟩, ?_⟩
    · rintro ⟨rfl, rfl⟩
      exact hns hroot
    · rintro (⟨hs, -⟩ | he)
      · exact hns hs
      · exact hyt he

/-- The swap maps the exterior onto itself. -/
theorem exterior_swap {p : Fin (k + 1) × Fin (k + 1)} (hp : p ∈ exterior D x y t) :
    (nnSwap x y p.1, nnSwap x y p.2) ∈ exterior D x y t := by
  obtain ⟨a, b⟩ := p
  rw [mem_exterior] at hp ⊢
  obtain ⟨⟨hn, hns⟩, hxy, hyt⟩ := hp
  simp only [ne_eq, Prod.mk.injEq] at hxy hyt ⊢
  have hab : a < b := naturalRel_forward hD hn
  have hxy' := h.xy_lt
  have hsucc := h.succ
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- natural
    by_cases ha : a = x
    · subst ha
      have hb : b ≠ a ∧ b ≠ y := ⟨hab.ne', fun hb => hxy ⟨rfl, hb⟩⟩
      rw [Equiv.swap_apply_left, swap_fix hb.1 hb.2]
      have hyb : y < b := by
        rw [Fin.lt_def, hsucc]
        have : a.val < b.val := hab
        have : b.val ≠ y.val := fun he => hb.2 (Fin.ext he)
        lia
      exact (naturalRel_interval hD hn hxy' hyb).2
    by_cases hay : a = y
    · subst hay
      have hb : b ≠ x ∧ b ≠ a := ⟨(hxy'.trans hab).ne', hab.ne'⟩
      rw [Equiv.swap_apply_right, swap_fix hb.1 hb.2]
      have hbt : b ≤ t := by
        by_contra hbt
        exact absurd (h.gap a b hn (lt_of_not_ge hbt)) (lt_irrefl a)
      have hbt' : b < t := lt_of_le_of_ne hbt fun he => hyt ⟨rfl, he⟩
      exact (naturalRel_interval hD (naturalRel_of_strictRel h.root)
        (hxy'.trans hab) hbt').1
    rw [swap_fix ha hay]
    by_cases hbx : b = x
    · subst hbx
      rw [Equiv.swap_apply_left]
      exact (h.boundary a hab).mp hn
    by_cases hby : b = y
    · subst hby
      rw [Equiv.swap_apply_right]
      have hax : a < x := by
        rw [Fin.lt_def]
        have : a.val < b.val := hab
        have : a.val ≠ x.val := fun he => ha (Fin.ext he)
        lia
      exact (h.boundary a hax).mpr hn
    rw [swap_fix hbx hby]
    exact hn
  · -- not strict
    intro hs
    rcases h.strict_cases hs with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · rw [swap_eq_x] at h1
      rw [h.swap_eq_t] at h2
      exact hyt ⟨h1, h2⟩
    · rw [swap_back h1 h2, swap_back h3 h4] at hs
      exact hns hs
  · rintro ⟨h1, h2⟩
    rw [swap_eq_x] at h1
    rw [swap_eq_y] at h2
    subst h1 h2
    exact absurd hab (not_lt_of_gt hxy')
  · rintro ⟨h1, h2⟩
    rw [swap_eq_y] at h1
    rw [h.swap_eq_t] at h2
    subst h1 h2
    exact hns h.root

theorem exterior_subset_target : exterior D x y t ⊆ normalPairs (nnTarget hD h) := by
  rw [← h.normalPairs_target_erase hD]
  exact Finset.erase_subset _ _

/-- The states without local shorts correspond under the swap. -/
theorem bottom_selected {Q : Finset (Fin (k + 1) × Fin (k + 1))}
    (hQ : Q ⊆ exterior D x y t) (u w : Fin (k + 1)) :
    D.edgeData.selected (stateOf hD Q).val u w ↔
      (nnTarget hD h).edgeData.selected
        (stateOf (nnTarget_forward hD h) (relabelPairs (nnSwap x y) Q)).val
        (nnSwap x y u) (nnSwap x y w) := by
  rw [stateOf_selected, stateOf_selected, h.strictRel_swap hD, mem_relabelPairs]
  constructor
  · rintro (hs | ⟨hq, -⟩)
    · exact Or.inl hs
    · refine Or.inr ⟨hq, ?_⟩
      exact (mem_normalPairs.mp (h.exterior_subset_target hD
        (h.exterior_swap hD (hQ hq)))).1
  · rintro (hs | ⟨hq, -⟩)
    · exact Or.inl hs
    · exact Or.inr ⟨hq, ((mem_exterior.mp (hQ hq)).1).1⟩

/-- The states with both local shorts have the same closure. -/
theorem top_transGen {Q : Finset (Fin (k + 1) × Fin (k + 1))} (hQ : Q ⊆ exterior D x y t) :
    Relation.TransGen (D.edgeData.selected (stateOf hD (insert (x, y) (insert (y, t) Q))).val) =
      Relation.TransGen ((nnTarget hD h).edgeData.selected
        (stateOf (nnTarget_forward hD h) (insert (x, y) Q)).val) := by
  have hxtQ : (x, t) ∉ Q := fun hq => (mem_exterior.mp (hQ hq)).1.2 h.root
  apply transGen_eq_of_le_of_le_transGen
  · intro u w huw
    rw [stateOf_selected, nnTarget_strictRel, nnTarget_naturalRel] at huw
    rw [stateOf_selected]
    rcases huw with (⟨hs, -⟩ | ⟨hu, hw⟩) | ⟨hq, hn, -⟩
    · exact Or.inl hs
    · rw [hu, hw]
      exact Or.inr ⟨by simp, h.nat_yt hD⟩
    · refine Or.inr ⟨?_, hn⟩
      rcases Finset.mem_insert.mp hq with he | hq
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hq)
  · intro u w huw
    rw [stateOf_selected] at huw
    have hsel (a b : Fin (k + 1)) (hab : (nnTarget hD h).edgeData.selected
        (stateOf (nnTarget_forward hD h) (insert (x, y) Q)).val a b) :
        Relation.TransGen ((nnTarget hD h).edgeData.selected
          (stateOf (nnTarget_forward hD h) (insert (x, y) Q)).val) a b :=
      Relation.TransGen.single hab
    have hxyR : (nnTarget hD h).edgeData.selected
        (stateOf (nnTarget_forward hD h) (insert (x, y) Q)).val x y := by
      rw [stateOf_selected, nnTarget_naturalRel]
      exact Or.inr ⟨Finset.mem_insert_self _ _, h.xy, fun he => h.t_ne_y he.2.symm⟩
    have hytR : (nnTarget hD h).edgeData.selected
        (stateOf (nnTarget_forward hD h) (insert (x, y) Q)).val y t := by
      rw [stateOf_selected, nnTarget_strictRel]
      exact Or.inl (Or.inr ⟨rfl, rfl⟩)
    rcases huw with hs | ⟨hq, hn⟩
    · by_cases hf : u = x ∧ w = t
      · rw [hf.1, hf.2]
        exact Relation.TransGen.head hxyR (Relation.TransGen.single hytR)
      · apply hsel
        rw [stateOf_selected, nnTarget_strictRel]
        exact Or.inl (Or.inl ⟨hs, hf⟩)
    · rcases Finset.mem_insert.mp hq with he | hq
      · rw [(Prod.mk.inj he).1, (Prod.mk.inj he).2]
        exact hsel _ _ hxyR
      rcases Finset.mem_insert.mp hq with he | hq
      · rw [(Prod.mk.inj he).1, (Prod.mk.inj he).2]
        exact hsel _ _ hytR
      · apply hsel
        rw [stateOf_selected, nnTarget_naturalRel]
        refine Or.inr ⟨Finset.mem_insert_of_mem hq, hn, ?_⟩
        rintro ⟨hu, hw⟩
        rw [hu, hw] at hq
        exact hxtQ hq

/-- **NN on full layers.** -/
theorem layer (s m : ℕ) (β : Fin m) :
    layerK D (Fin.last k) (s + 1) m β =
        layerK (nnTarget hD h) (Fin.last k) (s + 1) m β +
          layerK (nnTarget hD h) (Fin.last k) s m β ∧
      layerE D (Fin.last k) (s + 1) m β =
        layerE (nnTarget hD h) (Fin.last k) (s + 1) m β +
          layerE (nnTarget hD h) (Fin.last k) s m β := by
  have hR := nnTarget_forward hD h
  have hq : (x, y) ∉ exterior D x y t := fun hp => (mem_exterior.mp hp).2.1 rfl
  have hr : (y, t) ∉ exterior D x y t := fun hp => (mem_exterior.mp hp).2.2 rfl
  have hmaps : ∀ p ∈ exterior D x y t, (nnSwap x y p.1, nnSwap x y p.2) ∈ exterior D x y t :=
    fun p hp => h.exterior_swap hD hp
  have hσ : ∀ φ : Finset (Fin (k + 1) × Fin (k + 1)) → XPoly m,
      ∑ P ∈ (exterior D x y t).powerset, φ P =
        ∑ Q ∈ (exterior D x y t).powerset, φ (relabelPairs (nnSwap x y) Q) :=
    fun φ => sum_powerset_relabel (fun v => nnSwap_involutive v) hmaps φ
  have hQ (Q) (hQ : Q ∈ (exterior D x y t).powerset) : Q ⊆ exterior D x y t :=
    Finset.mem_powerset.mp hQ
  have hdia (Q) (hQ' : Q ∈ (exterior D x y t).powerset) :=
    stateOf_diamond hD Q h.xy (h.nat_yt hD) ((stateOf_selected hD Q x t).mpr (Or.inl h.root))
      (Fin.last k) m β
  have hbot (Q) (hQ' : Q ∈ (exterior D x y t).powerset) :
      markedK (stateOf hR (relabelPairs (nnSwap x y) Q)) (Fin.last k) m β =
          markedK (stateOf hD Q) (Fin.last k) m β ∧
        markedE (stateOf hR (relabelPairs (nnSwap x y) Q)) (Fin.last k) m β =
          markedE (stateOf hD Q) (Fin.last k) m β :=
    ⟨(markedK_relabel _ _ (nnSwap x y) (h.bottom_selected hD (hQ Q hQ')) _
        h.swap_last m β).symm,
      (markedE_relabel_of_sinkOrder _ _ hD hR (nnSwap x y) (h.bottom_selected hD (hQ Q hQ'))
        (swap_sinkOrder h.succ ((stateOf_selected hD Q x t).mpr (Or.inl h.root))) _
        (fun u => Fin.le_last u) h.swap_last m β).symm⟩
  have htop (Q) (hQ' : Q ∈ (exterior D x y t).powerset) :=
    markedValues_eq_of_transGen_eq hR hD _ _ (h.top_transGen hD (hQ Q hQ')).symm
      (Fin.last k) m β
  unfold layerK layerE
  simp only [sum_edgeLayer_eq hD, sum_edgeLayer_eq hR]
  rw [sum_powerset_two h.normal_xy (h.normal_yt hD) h.pair_ne,
    sum_powerset_two h.normal_xy (h.normal_yt hD) h.pair_ne,
    sum_powerset_one (h.normalPairs_target_xy hD), sum_powerset_one (h.normalPairs_target_xy hD),
    sum_powerset_one (h.normalPairs_target_xy hD), sum_powerset_one (h.normalPairs_target_xy hD),
    h.normalPairs_target_erase hD, h.card_strictPairs_target hD]
  exact ⟨nn_sum_algebra hq hr h.pair_ne _ s _ _ _ hσ (fun Q _ => card_relabelPairs _ Q)
      (fun Q hQ => (hdia Q hQ).1) (fun Q hQ => (hbot Q hQ).1) (fun Q hQ => (htop Q hQ).1),
    nn_sum_algebra hq hr h.pair_ne _ s _ _ _ hσ (fun Q _ => card_relabelPairs _ Q)
      (fun Q hQ => (hdia Q hQ).2) (fun Q hQ => (hbot Q hQ).2) (fun Q hQ => (htop Q hQ).2)⟩

/-- The NN target has smaller natural area. -/
theorem target_measureLT : MeasureLT (nnTarget hD h) D := by
  left
  apply naturalArea_lt_of_ssubset
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(x, t), mem_naturalPairs.mpr (naturalRel_of_strictRel h.root), ?_⟩
    rw [mem_naturalPairs, nnTarget_naturalRel]
    exact fun he => he.2 ⟨rfl, rfl⟩
  · intro p hp
    exact mem_naturalPairs.mpr ((nnTarget_naturalRel hD h _ _).mp (mem_naturalPairs.mp hp)).1

end NNContact

end

end VerticalStripLLT.Circular.DiagramProof
