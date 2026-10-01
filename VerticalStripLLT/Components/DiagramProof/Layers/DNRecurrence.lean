import VerticalStripLLT.Components.DiagramProof.Layers.NNRecurrence

/-!
# The forward DN recurrence on full edge layers

At a DN contact the strict incoming corner `ux` meets the strict root `xt`, with
local shorts `q = xy` and `r = yt`, where `y = x + 1`. The target replaces the
natural edge `xt` by `uy`; there `uy` and `yt` are strict and `p = ux`, `q = xy`
are the local shorts. Diamonds at `x < y < t` in the source and at `u < x < y`
in the target, the swap of `x, y` on the states with neither short and closure
equality on the states with both give, at every fixed colour of the greatest vertex,

    X(layer_s L) = X(layer_s R),   X = K, E.

The target has the same natural area and smaller area moment.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-! ### The algebra of the split -/

section Algebra

variable {α M : Type*} [DecidableEq α] [AddCommGroup M]

/-- Collapse the four local terms of a split by its diamond. -/
theorem four_sum_canon {X : Finset α} {q r : α} (hq : q ∉ X) (hr : r ∉ X) (hqr : q ≠ r)
    (c s : ℕ) (f : Finset α → M)
    (hdia : ∀ Q ∈ X.powerset,
      f (insert q Q) + f (insert r Q) = f Q + f (insert q (insert r Q))) :
    ∑ Q ∈ X.powerset,
        ((if c + Q.card = s then f Q else 0) +
          (if c + (insert q Q).card = s then f (insert q Q) else 0) +
          (if c + (insert r Q).card = s then f (insert r Q) else 0) +
          (if c + (insert q (insert r Q)).card = s then f (insert q (insert r Q)) else 0)) =
      ∑ Q ∈ X.powerset, ((if c + Q.card = s then f Q else 0) +
          (if c + Q.card + 1 = s then f Q else 0)) +
        ∑ Q ∈ X.powerset, ((if c + Q.card + 1 = s then f (insert q (insert r Q)) else 0) +
          (if c + Q.card + 1 + 1 = s then f (insert q (insert r Q)) else 0)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have hcqr : (insert q (insert r Q)).card = Q.card + 1 + 1 := by
    rw [Finset.card_insert_of_notMem, card_insert_of_mem_powerset hr hQ]
    intro hm
    rcases Finset.mem_insert.mp hm with he | hm
    · exact hqr he
    · exact hq (Finset.mem_powerset.mp hQ hm)
  rw [hcqr, card_insert_of_mem_powerset hq hQ]
  simp only [card_insert_of_mem_powerset hr hQ, ← add_assoc]
  by_cases hc : c + Q.card + 1 = s
  · simp only [hc, ite_true]
    rw [add_assoc (ite _ _ _) (f (insert q Q)), hdia Q hQ]
    abel
  · simp only [hc, ite_false]
    try abel

/-- The layer bookkeeping of the DN recurrence. -/
theorem dn_sum_algebra {X : Finset α} {q r p q' : α} (hq : q ∉ X) (hr : r ∉ X) (hqr : q ≠ r)
    (hp : p ∉ X) (hq' : q' ∉ X) (hpq : p ≠ q') (c s : ℕ) (f g : Finset α → M)
    (σ : Finset α → Finset α)
    (hσ : ∀ φ : Finset α → M, ∑ P ∈ X.powerset, φ P = ∑ Q ∈ X.powerset, φ (σ Q))
    (hσcard : ∀ Q ∈ X.powerset, (σ Q).card = Q.card)
    (hdiaL : ∀ Q ∈ X.powerset,
      f (insert q Q) + f (insert r Q) = f Q + f (insert q (insert r Q)))
    (hdiaR : ∀ Q ∈ X.powerset,
      g (insert p Q) + g (insert q' Q) = g Q + g (insert p (insert q' Q)))
    (h0 : ∀ Q ∈ X.powerset, g (σ Q) = f Q)
    (h11 : ∀ Q ∈ X.powerset, g (insert p (insert q' Q)) = f (insert q (insert r Q))) :
    ∑ Q ∈ X.powerset,
        ((if c + Q.card = s then f Q else 0) +
          (if c + (insert q Q).card = s then f (insert q Q) else 0) +
          (if c + (insert r Q).card = s then f (insert r Q) else 0) +
          (if c + (insert q (insert r Q)).card = s then f (insert q (insert r Q)) else 0)) =
      ∑ Q ∈ X.powerset,
        ((if c + Q.card = s then g Q else 0) +
          (if c + (insert p Q).card = s then g (insert p Q) else 0) +
          (if c + (insert q' Q).card = s then g (insert q' Q) else 0) +
          (if c + (insert p (insert q' Q)).card = s then g (insert p (insert q' Q)) else 0)) := by
  rw [four_sum_canon hq hr hqr c s f hdiaL, four_sum_canon hp hq' hpq c s g hdiaR,
    hσ (fun Q => (if c + Q.card = s then g Q else 0) + (if c + Q.card + 1 = s then g Q else 0))]
  congr 1
  · refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [hσcard Q hQ, h0 Q hQ]
  · refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [h11 Q hQ]

end Algebra

/-! ### The contact and its target -/

variable {k : ℕ} {D : Diagram (k + 1)} (hD : Forward D)

/-- An eligible forward DN contact: the strict incoming corner `ux` and the strict
root `xt`, with `y = x + 1`. -/
structure DNContact (D : Diagram (k + 1)) (u x y t : Fin (k + 1)) : Prop where
  succ : y.val = x.val + 1
  ux : u < x
  yt : y < t
  root : strictRel D x t
  incoming : strictRel D u x
  gap : ∀ p q, naturalRel D p q → t < q → y < p
  boundary : ∀ p, p < x → (naturalRel D p y ↔ naturalRel D p x ∧ p ≠ u)
  xy : naturalRel D x y
  tailx : ∀ b, strictRel D x b → b = t
  taily : ∀ b, ¬ strictRel D y b
  headx : ∀ a, strictRel D a x → a = u
  heady : ∀ a, ¬ strictRel D a y

namespace DNContact

variable {u x y t : Fin (k + 1)} (h : DNContact D u x y t)

include h

theorem xy_lt : x < y := by
  rw [Fin.lt_def, h.succ]
  lia

theorem ne_xy : x ≠ y := h.xy_lt.ne

theorem u_ne_x : u ≠ x := h.ux.ne

theorem u_ne_y : u ≠ y := (h.ux.trans h.xy_lt).ne

theorem t_ne_x : t ≠ x := (h.xy_lt.trans h.yt).ne'

theorem t_ne_y : t ≠ y := h.yt.ne'

theorem not_nat_uy : ¬ naturalRel D u y := fun huy => ((h.boundary u h.ux).mp huy).2 rfl

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

theorem pair_ne' : ((u, x) : Fin (k + 1) × Fin (k + 1)) ≠ (x, y) := by
  intro he
  exact h.u_ne_x (Prod.mk.inj he).1

/-- The strict pairs touching `x` or `y` are exactly the root and the incoming corner. -/
theorem strict_cases {a b : Fin (k + 1)} (hab : strictRel D a b) :
    (a = x ∧ b = t) ∨ (a = u ∧ b = x) ∨ (a ≠ x ∧ a ≠ y ∧ b ≠ x ∧ b ≠ y) := by
  by_cases ha : a = x
  · rw [ha] at hab ⊢
    exact Or.inl ⟨rfl, h.tailx b hab⟩
  by_cases hb : b = x
  · rw [hb] at hab ⊢
    exact Or.inr (Or.inl ⟨h.headx a hab, rfl⟩)
  refine Or.inr (Or.inr ⟨ha, ?_, hb, ?_⟩)
  · intro hay
    rw [hay] at hab
    exact h.taily b hab
  · intro hby
    rw [hby] at hab
    exact h.heady a hab

end DNContact

/-! ### The target diagram -/

variable {u x y t : Fin (k + 1)} (h : DNContact D u x y t)

/-- The natural relation of the DN target. -/
def dnNatural (D : Diagram (k + 1)) (u x y t : Fin (k + 1)) (a b : Fin (k + 1)) : Prop :=
  (naturalRel D a b ∧ ¬ (a = x ∧ b = t)) ∨ (a = u ∧ b = y)

/-- The strict relation of the DN target. -/
def dnStrict (D : Diagram (k + 1)) (u x y t : Fin (k + 1)) (a b : Fin (k + 1)) : Prop :=
  (strictRel D a b ∧ ¬ (a = x ∧ b = t) ∧ ¬ (a = u ∧ b = x)) ∨ (a = u ∧ b = y) ∨
    (a = y ∧ b = t)

namespace DNContact

include h hD

theorem dnNatural_ordinary : OrdinaryRelation (dnNatural D u x y t) := by
  have hxt := maximalPair_of_strictRel hD h.root
  refine ⟨?_, ?_⟩
  · rintro a b (⟨hn, -⟩ | ⟨rfl, rfl⟩)
    · exact naturalRel_forward hD hn
    · exact h.ux.trans h.xy_lt
  · rintro a v b (⟨hn, hne⟩ | ⟨ha, hb⟩) hav hvb
    · obtain ⟨h1, h2⟩ := naturalRel_interval hD hn hav hvb
      refine ⟨Or.inl ⟨h1, ?_⟩, Or.inl ⟨h2, ?_⟩⟩
      · rintro ⟨rfl, rfl⟩
        exact hvb.ne (hxt.2 a b hn le_rfl hvb.le).2.symm
      · rintro ⟨rfl, rfl⟩
        exact hav.ne (hxt.2 a b hn hav.le le_rfl).1
    · rw [ha] at hav
      rw [hb] at hvb
      rw [ha, hb]
      have hvx : v ≤ x := by
        rw [Fin.le_def]
        have : v.val < y.val := hvb
        have := h.succ
        lia
      have huv : naturalRel D u v := by
        rcases lt_or_eq_of_le hvx with hvx | rfl
        · exact (naturalRel_interval hD (naturalRel_of_strictRel h.incoming) hav hvx).1
        · exact naturalRel_of_strictRel h.incoming
      have hvy : naturalRel D v y := by
        rcases lt_or_eq_of_le hvx with hvx' | rfl
        · exact (h.boundary v hvx').mpr
            ⟨(naturalRel_interval hD (naturalRel_of_strictRel h.incoming) hav hvx').2,
              hav.ne'⟩
        · exact h.xy
      refine ⟨Or.inl ⟨huv, fun he => h.u_ne_x he.1⟩, Or.inl ⟨hvy, fun he => h.t_ne_y he.2.symm⟩⟩

theorem dnStrict_maximal (a b : Fin (k + 1)) (hab : dnStrict D u x y t a b) :
    MaximalPair (dnNatural D u x y t) a b := by
  -- Natural pairs of the target containing a vertex at or before `u` and ending at
  -- or beyond `y` are only `uy`.
  have hcont : ∀ p q, dnNatural D u x y t p q → p ≤ u → y ≤ q → p = u ∧ q = y := by
    rintro p q (⟨hn, -⟩ | ⟨rfl, rfl⟩) hpu hyq
    · exfalso
      have hpy : naturalRel D p y := by
        rcases lt_or_eq_of_le hyq with hyq | rfl
        · exact (naturalRel_interval hD hn ((hpu.trans_lt h.ux).trans h.xy_lt) hyq).1
        · exact hn
      obtain ⟨hpx, hpu'⟩ := (h.boundary p (hpu.trans_lt h.ux)).mp hpy
      have := (maximalPair_of_strictRel hD h.incoming).2 p x hpx hpu le_rfl
      exact hpu' this.1
    · exact ⟨rfl, rfl⟩
  rcases hab with ⟨hs, hne1, hne2⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine ⟨Or.inl ⟨naturalRel_of_strictRel hs, hne1⟩, ?_⟩
    rintro p q (⟨hn, -⟩ | ⟨hp, hq⟩) hpa hbq
    · exact strictRel_maximal hD hs hn hpa hbq
    · exfalso
      rw [hp] at hpa
      rw [hq] at hbq
      rcases h.strict_cases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h2, h3, h4⟩
      · exact hne1 ⟨rfl, rfl⟩
      · exact hne2 ⟨rfl, rfl⟩
      · have hbx : b < x := by
          rw [Fin.lt_def]
          have : b.val ≤ y.val := hbq
          have := h.succ
          have : b.val ≠ x.val := fun he => h3 (Fin.ext he)
          have : b.val ≠ y.val := fun he => h4 (Fin.ext he)
          lia
        have := (maximalPair_of_strictRel hD hs).2 u x (naturalRel_of_strictRel h.incoming)
          hpa hbx.le
        exact h3 this.2.symm
  · rw [ha, hb]
    exact ⟨Or.inr ⟨rfl, rfl⟩, fun p q hpq hpu hyq => hcont p q hpq hpu hyq⟩
  · rw [ha, hb]
    refine ⟨Or.inl ⟨h.nat_yt hD, fun he => h.ne_xy he.1.symm⟩, ?_⟩
    rintro p q (⟨hn, hne⟩ | ⟨hp, hq⟩) hpy htq
    · have hq : q = t := by
        by_contra hqt
        exact absurd hpy (not_le_of_gt (h.gap p q hn (lt_of_le_of_ne htq (Ne.symm hqt))))
      rw [hq] at hn hne ⊢
      refine ⟨?_, rfl⟩
      by_cases hpx : p ≤ x
      · have := strictRel_maximal hD h.root hn hpx le_rfl
        exact (hne ⟨this.1, rfl⟩).elim
      · apply le_antisymm hpy
        rw [Fin.le_def, h.succ]
        have : x.val < p.val := lt_of_not_ge hpx
        lia
    · exfalso
      rw [hq] at htq
      exact absurd htq (not_le_of_gt h.yt)

end DNContact

/-- The DN target: the natural edge `xt` is replaced by the strict pair `uy`. -/
def dnTarget : Diagram (k + 1) :=
  ofRelations (dnNatural D u x y t) (dnStrict D u x y t) (h.dnNatural_ordinary hD)
    (h.dnStrict_maximal hD) D.area.positive

theorem dnTarget_forward : Forward (dnTarget hD h) := ofRelations_forward _ _ _ _ _

theorem dnTarget_naturalRel (a b : Fin (k + 1)) :
    naturalRel (dnTarget hD h) a b ↔ dnNatural D u x y t a b :=
  ofRelations_naturalRel ..

theorem dnTarget_strictRel (a b : Fin (k + 1)) :
    strictRel (dnTarget hD h) a b ↔ dnStrict D u x y t a b :=
  ofRelations_strictRel ..

namespace DNContact

include h hD

omit hD in
theorem swap_u : nnSwap x y u = u := NNContact.swap_fix h.u_ne_x h.u_ne_y

omit hD in
theorem swap_t : nnSwap x y t = t := NNContact.swap_fix h.t_ne_x h.t_ne_y

omit hD in
theorem swap_last : nnSwap x y (Fin.last k) = Fin.last k := by
  apply NNContact.swap_fix
  · exact ((h.xy_lt.trans h.yt).trans_le (Fin.le_last t)).ne'
  · exact (h.yt.trans_le (Fin.le_last t)).ne'

omit hD in
theorem swap_eq_u {a : Fin (k + 1)} : nnSwap x y a = u ↔ a = u := by
  rw [Equiv.swap_apply_eq_iff, h.swap_u]

omit hD in
theorem swap_eq_t {a : Fin (k + 1)} : nnSwap x y a = t ↔ a = t := by
  rw [Equiv.swap_apply_eq_iff, h.swap_t]

/-- Strict pairs correspond under the swap. -/
theorem strictRel_swap (a b : Fin (k + 1)) :
    strictRel (dnTarget hD h) (nnSwap x y a) (nnSwap x y b) ↔ strictRel D a b := by
  rw [dnTarget_strictRel]
  unfold dnStrict
  constructor
  · rintro (⟨hs, hne1, hne2⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩)
    · rcases h.strict_cases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
      · exact (hne1 ⟨h1, h2⟩).elim
      · exact (hne2 ⟨h1, h2⟩).elim
      · rw [NNContact.swap_back h1 h2, NNContact.swap_back h3 h4] at hs
        exact hs
    · rw [h.swap_eq_u] at ha
      rw [NNContact.swap_eq_y] at hb
      rw [ha, hb]
      exact h.incoming
    · rw [NNContact.swap_eq_y] at ha
      rw [h.swap_eq_t] at hb
      rw [ha, hb]
      exact h.root
  · intro hs
    rcases h.strict_cases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨h1, h2, h3, h4⟩
    · rw [ha, hb, Equiv.swap_apply_left, h.swap_t]
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · rw [ha, hb, h.swap_u, Equiv.swap_apply_left]
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rw [NNContact.swap_fix h1 h2, NNContact.swap_fix h3 h4]
      exact Or.inl ⟨hs, fun he => h1 he.1, fun he => h3 he.2⟩

theorem card_strictPairs_target :
    (strictPairs (dnTarget hD h)).card = (strictPairs D).card := by
  have : strictPairs (dnTarget hD h) = relabelPairs (nnSwap x y) (strictPairs D) := by
    ext ⟨a', b'⟩
    obtain ⟨a, rfl⟩ := (nnSwap x y).surjective a'
    obtain ⟨b, rfl⟩ := (nnSwap x y).surjective b'
    rw [mem_relabelPairs, mem_strictPairs, mem_strictPairs]
    exact h.strictRel_swap hD a b
  rw [this, card_relabelPairs]

theorem normal_ux_target : (u, x) ∈ normalPairs (dnTarget hD h) := by
  rw [mem_normalPairs, dnTarget_naturalRel, dnTarget_strictRel]
  unfold dnNatural dnStrict
  refine ⟨Or.inl ⟨naturalRel_of_strictRel h.incoming, fun he => h.u_ne_x he.1⟩, ?_⟩
  rintro (⟨-, -, hne⟩ | ⟨-, he⟩ | ⟨he, -⟩)
  · exact hne ⟨rfl, rfl⟩
  · exact h.ne_xy he
  · exact h.u_ne_y he

theorem normal_xy_target : (x, y) ∈ normalPairs (dnTarget hD h) := by
  rw [mem_normalPairs, dnTarget_naturalRel, dnTarget_strictRel]
  unfold dnNatural dnStrict
  refine ⟨Or.inl ⟨h.xy, fun he => h.t_ne_y he.2.symm⟩, ?_⟩
  rintro (⟨hs, -, -⟩ | ⟨he, -⟩ | ⟨he, -⟩)
  · exact h.heady x hs
  · exact h.u_ne_x he.symm
  · exact h.ne_xy he

theorem normalPairs_target_erase :
    ((normalPairs (dnTarget hD h)).erase (u, x)).erase (x, y) =
      NNContact.exterior D x y t := by
  ext ⟨a, b⟩
  rw [NNContact.mem_exterior (D := D) (x := x) (y := y) (t := t), Finset.mem_erase,
    Finset.mem_erase, mem_normalPairs, dnTarget_naturalRel, dnTarget_strictRel]
  unfold dnNatural dnStrict
  constructor
  · rintro ⟨hxy, hux, ⟨hn, hxt⟩ | ⟨ha, hb⟩, hns⟩
    · refine ⟨⟨hn, fun hs => hns (Or.inl ⟨hs, hxt, fun he => hux ?_⟩)⟩, hxy, ?_⟩
      · exact Prod.ext he.1 he.2
      · intro he
        exact hns (Or.inr (Or.inr (Prod.mk.inj he)))
    · exact (hns (Or.inr (Or.inl ⟨ha, hb⟩))).elim
  · rintro ⟨⟨hn, hns⟩, hxy, hyt⟩
    refine ⟨hxy, ?_, Or.inl ⟨hn, ?_⟩, ?_⟩
    · intro he
      rw [(Prod.mk.inj he).1, (Prod.mk.inj he).2] at hns
      exact hns h.incoming
    · rintro ⟨ha, hb⟩
      rw [ha, hb] at hns
      exact hns h.root
    · rintro (⟨hs, -, -⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩)
      · exact hns hs
      · rw [ha, hb] at hn
        exact h.not_nat_uy hn
      · exact hyt (Prod.ext ha hb)

theorem exterior_subset_target :
    NNContact.exterior D x y t ⊆ normalPairs (dnTarget hD h) := by
  rw [← h.normalPairs_target_erase hD]
  exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)

/-- The swap maps the exterior onto itself. -/
theorem exterior_swap {p : Fin (k + 1) × Fin (k + 1)} (hp : p ∈ NNContact.exterior D x y t) :
    (nnSwap x y p.1, nnSwap x y p.2) ∈ NNContact.exterior D x y t := by
  obtain ⟨a, b⟩ := p
  rw [NNContact.mem_exterior] at hp ⊢
  obtain ⟨⟨hn, hns⟩, hxy, hyt⟩ := hp
  simp only [ne_eq, Prod.mk.injEq] at hxy hyt ⊢
  have hab : a < b := naturalRel_forward hD hn
  have hxy' := h.xy_lt
  have hsucc := h.succ
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · by_cases ha : a = x
    · rw [ha] at hn hab hxy hyt ⊢
      have hb : b ≠ x ∧ b ≠ y := ⟨hab.ne', fun hb => hxy ⟨rfl, hb⟩⟩
      rw [Equiv.swap_apply_left, NNContact.swap_fix hb.1 hb.2]
      have hyb : y < b := by
        rw [Fin.lt_def, hsucc]
        have : x.val < b.val := hab
        have : b.val ≠ y.val := fun he => hb.2 (Fin.ext he)
        lia
      exact (naturalRel_interval hD hn hxy' hyb).2
    by_cases hay : a = y
    · rw [hay] at hn hab hxy hyt ⊢
      have hb : b ≠ x ∧ b ≠ y := ⟨(hxy'.trans hab).ne', hab.ne'⟩
      rw [Equiv.swap_apply_right, NNContact.swap_fix hb.1 hb.2]
      have hbt : b ≤ t := by
        by_contra hbt
        exact absurd (h.gap y b hn (lt_of_not_ge hbt)) (lt_irrefl y)
      have hbt' : b < t := lt_of_le_of_ne hbt fun he => hyt ⟨rfl, he⟩
      exact (naturalRel_interval hD (naturalRel_of_strictRel h.root)
        (hxy'.trans hab) hbt').1
    rw [NNContact.swap_fix ha hay]
    by_cases hbx : b = x
    · rw [hbx] at hn hab hns ⊢
      rw [Equiv.swap_apply_left]
      have hau : a ≠ u := by
        rintro rfl
        exact hns h.incoming
      exact (h.boundary a hab).mpr ⟨hn, hau⟩
    by_cases hby : b = y
    · rw [hby] at hn hab ⊢
      rw [Equiv.swap_apply_right]
      have hax : a < x := by
        rw [Fin.lt_def]
        have : a.val < y.val := hab
        have : a.val ≠ x.val := fun he => ha (Fin.ext he)
        lia
      exact ((h.boundary a hax).mp hn).1
    rw [NNContact.swap_fix hbx hby]
    exact hn
  · intro hs
    rcases h.strict_cases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · rw [NNContact.swap_eq_x] at h1
      rw [h.swap_eq_t] at h2
      exact hyt ⟨h1, h2⟩
    · rw [h.swap_eq_u] at h1
      rw [NNContact.swap_eq_x] at h2
      rw [h1, h2] at hn
      exact h.not_nat_uy hn
    · rw [NNContact.swap_back h1 h2, NNContact.swap_back h3 h4] at hs
      exact hns hs
  · rintro ⟨h1, h2⟩
    rw [NNContact.swap_eq_x] at h1
    rw [NNContact.swap_eq_y] at h2
    rw [h1, h2] at hab
    exact absurd hab (not_lt_of_gt hxy')
  · rintro ⟨h1, h2⟩
    rw [NNContact.swap_eq_y] at h1
    rw [h.swap_eq_t] at h2
    rw [h1, h2] at hns
    exact hns h.root

/-- The states without local shorts correspond under the swap. -/
theorem bottom_selected {Q : Finset (Fin (k + 1) × Fin (k + 1))}
    (hQ : Q ⊆ NNContact.exterior D x y t) (a b : Fin (k + 1)) :
    D.edgeData.selected (stateOf hD Q).val a b ↔
      (dnTarget hD h).edgeData.selected
        (stateOf (dnTarget_forward hD h) (relabelPairs (nnSwap x y) Q)).val
        (nnSwap x y a) (nnSwap x y b) := by
  rw [stateOf_selected, stateOf_selected, h.strictRel_swap hD, mem_relabelPairs]
  constructor
  · rintro (hs | ⟨hq, -⟩)
    · exact Or.inl hs
    · exact Or.inr ⟨hq, (mem_normalPairs.mp (h.exterior_subset_target hD
        (h.exterior_swap hD (hQ hq)))).1⟩
  · rintro (hs | ⟨hq, -⟩)
    · exact Or.inl hs
    · exact Or.inr ⟨hq, ((NNContact.mem_exterior.mp (hQ hq)).1).1⟩

/-- The states with both local shorts have the same closure. -/
theorem top_transGen {Q : Finset (Fin (k + 1) × Fin (k + 1))}
    (hQ : Q ⊆ NNContact.exterior D x y t) :
    Relation.TransGen (D.edgeData.selected (stateOf hD (insert (x, y) (insert (y, t) Q))).val) =
      Relation.TransGen ((dnTarget hD h).edgeData.selected
        (stateOf (dnTarget_forward hD h) (insert (u, x) (insert (x, y) Q))).val) := by
  have hR := dnTarget_forward hD h
  have hux : (dnTarget hD h).edgeData.selected
      (stateOf hR (insert (u, x) (insert (x, y) Q))).val u x :=
    (stateOf_selected hR _ u x).mpr (Or.inr ⟨Finset.mem_insert_self _ _,
      (mem_normalPairs.mp (h.normal_ux_target hD)).1⟩)
  have hxyR : (dnTarget hD h).edgeData.selected
      (stateOf hR (insert (u, x) (insert (x, y) Q))).val x y :=
    (stateOf_selected hR _ x y).mpr (Or.inr ⟨by simp,
      (mem_normalPairs.mp (h.normal_xy_target hD)).1⟩)
  have hytR : (dnTarget hD h).edgeData.selected
      (stateOf hR (insert (u, x) (insert (x, y) Q))).val y t :=
    (stateOf_selected hR _ y t).mpr (Or.inl ((dnTarget_strictRel hD h y t).mpr
      (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  have hxyL : D.edgeData.selected (stateOf hD (insert (x, y) (insert (y, t) Q))).val x y :=
    (stateOf_selected hD _ x y).mpr (Or.inr ⟨Finset.mem_insert_self _ _, h.xy⟩)
  have hytL : D.edgeData.selected (stateOf hD (insert (x, y) (insert (y, t) Q))).val y t :=
    (stateOf_selected hD _ y t).mpr (Or.inr ⟨by simp, h.nat_yt hD⟩)
  have huxL : D.edgeData.selected (stateOf hD (insert (x, y) (insert (y, t) Q))).val u x :=
    (stateOf_selected hD _ u x).mpr (Or.inl h.incoming)
  apply transGen_eq_of_le_transGen
  · intro a b hab
    rw [stateOf_selected] at hab
    rcases hab with hs | ⟨hq, hn⟩
    · rcases h.strict_cases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨h1, -, h3, -⟩
      · rw [ha, hb]
        exact Relation.TransGen.head hxyR (Relation.TransGen.single hytR)
      · rw [ha, hb]
        exact Relation.TransGen.single hux
      · apply Relation.TransGen.single
        rw [stateOf_selected, dnTarget_strictRel]
        exact Or.inl (Or.inl ⟨hs, fun he => h1 he.1, fun he => h3 he.2⟩)
    · rcases Finset.mem_insert.mp hq with he | hq
      · rw [(Prod.mk.inj he).1, (Prod.mk.inj he).2]
        exact Relation.TransGen.single hxyR
      rcases Finset.mem_insert.mp hq with he | hq
      · rw [(Prod.mk.inj he).1, (Prod.mk.inj he).2]
        exact Relation.TransGen.single hytR
      · apply Relation.TransGen.single
        rw [stateOf_selected]
        exact Or.inr ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hq),
          (mem_normalPairs.mp (h.exterior_subset_target hD (hQ hq))).1⟩
  · intro a b hab
    rw [stateOf_selected, dnTarget_strictRel, dnTarget_naturalRel] at hab
    unfold dnStrict dnNatural at hab
    rcases hab with (⟨hs, -, -⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨hq, hn⟩
    · exact Relation.TransGen.single ((stateOf_selected hD _ a b).mpr (Or.inl hs))
    · rw [ha, hb]
      exact Relation.TransGen.head huxL (Relation.TransGen.single hxyL)
    · rw [ha, hb]
      exact Relation.TransGen.single hytL
    · rcases Finset.mem_insert.mp hq with he | hq
      · rw [(Prod.mk.inj he).1, (Prod.mk.inj he).2]
        exact Relation.TransGen.single huxL
      rcases Finset.mem_insert.mp hq with he | hq
      · rw [(Prod.mk.inj he).1, (Prod.mk.inj he).2]
        exact Relation.TransGen.single hxyL
      · apply Relation.TransGen.single
        rw [stateOf_selected]
        exact Or.inr ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hq),
          ((NNContact.mem_exterior.mp (hQ hq)).1).1⟩

/-- **DN on full layers.** -/
theorem layer (s m : ℕ) (β : Fin m) :
    layerK D (Fin.last k) s m β = layerK (dnTarget hD h) (Fin.last k) s m β ∧
      layerE D (Fin.last k) s m β = layerE (dnTarget hD h) (Fin.last k) s m β := by
  have hR := dnTarget_forward hD h
  have hq : (x, y) ∉ NNContact.exterior D x y t := fun hp =>
    (NNContact.mem_exterior.mp hp).2.1 rfl
  have hr : (y, t) ∉ NNContact.exterior D x y t := fun hp =>
    (NNContact.mem_exterior.mp hp).2.2 rfl
  have hp : (u, x) ∉ NNContact.exterior D x y t := fun hp =>
    (NNContact.mem_exterior.mp hp).1.2 h.incoming
  have hmaps : ∀ p ∈ NNContact.exterior D x y t,
      (nnSwap x y p.1, nnSwap x y p.2) ∈ NNContact.exterior D x y t :=
    fun p hp => h.exterior_swap hD hp
  have hσ : ∀ φ : Finset (Fin (k + 1) × Fin (k + 1)) → XPoly m,
      ∑ P ∈ (NNContact.exterior D x y t).powerset, φ P =
        ∑ Q ∈ (NNContact.exterior D x y t).powerset, φ (relabelPairs (nnSwap x y) Q) :=
    fun φ => sum_powerset_relabel (fun v => nnSwap_involutive v) hmaps φ
  have hQ (Q) (hQ : Q ∈ (NNContact.exterior D x y t).powerset) :
      Q ⊆ NNContact.exterior D x y t := Finset.mem_powerset.mp hQ
  have hdiaL (Q) (_ : Q ∈ (NNContact.exterior D x y t).powerset) :=
    stateOf_diamond hD Q h.xy (h.nat_yt hD) ((stateOf_selected hD Q x t).mpr (Or.inl h.root))
      (Fin.last k) m β
  have hdiaR (Q) (_ : Q ∈ (NNContact.exterior D x y t).powerset) :=
    stateOf_diamond hR Q (mem_normalPairs.mp (h.normal_ux_target hD)).1
      (mem_normalPairs.mp (h.normal_xy_target hD)).1
      ((stateOf_selected hR Q u y).mpr (Or.inl ((dnTarget_strictRel hD h u y).mpr
        (Or.inr (Or.inl ⟨rfl, rfl⟩))))) (Fin.last k) m β
  have hbot (Q) (hQ' : Q ∈ (NNContact.exterior D x y t).powerset) :
      markedK (stateOf hR (relabelPairs (nnSwap x y) Q)) (Fin.last k) m β =
          markedK (stateOf hD Q) (Fin.last k) m β ∧
        markedE (stateOf hR (relabelPairs (nnSwap x y) Q)) (Fin.last k) m β =
          markedE (stateOf hD Q) (Fin.last k) m β :=
    ⟨(markedK_relabel _ _ (nnSwap x y) (h.bottom_selected hD (hQ Q hQ')) _
        (h.swap_last) m β).symm,
      (markedE_relabel_of_sinkOrder _ _ hD hR (nnSwap x y) (h.bottom_selected hD (hQ Q hQ'))
        (NNContact.swap_sinkOrder h.succ ((stateOf_selected hD Q x t).mpr (Or.inl h.root))) _
        (fun v => Fin.le_last v) (h.swap_last) m β).symm⟩
  have htop (Q) (hQ' : Q ∈ (NNContact.exterior D x y t).powerset) :=
    markedValues_eq_of_transGen_eq hR hD _ _ (h.top_transGen hD (hQ Q hQ')).symm
      (Fin.last k) m β
  unfold layerK layerE
  simp only [sum_edgeLayer_eq hD, sum_edgeLayer_eq hR]
  rw [sum_powerset_two h.normal_xy (h.normal_yt hD) h.pair_ne,
    sum_powerset_two h.normal_xy (h.normal_yt hD) h.pair_ne,
    sum_powerset_two (h.normal_ux_target hD) (h.normal_xy_target hD) h.pair_ne',
    sum_powerset_two (h.normal_ux_target hD) (h.normal_xy_target hD) h.pair_ne',
    h.normalPairs_target_erase hD, h.card_strictPairs_target hD]
  exact ⟨dn_sum_algebra hq hr h.pair_ne hp hq h.pair_ne' _ s _ _ _ hσ
      (fun Q _ => card_relabelPairs _ Q) (fun Q hQ => (hdiaL Q hQ).1)
      (fun Q hQ => (hdiaR Q hQ).1) (fun Q hQ => (hbot Q hQ).1) (fun Q hQ => (htop Q hQ).1),
    dn_sum_algebra hq hr h.pair_ne hp hq h.pair_ne' _ s _ _ _ hσ
      (fun Q _ => card_relabelPairs _ Q) (fun Q hQ => (hdiaL Q hQ).2)
      (fun Q hQ => (hdiaR Q hQ).2) (fun Q hQ => (hbot Q hQ).2) (fun Q hQ => (htop Q hQ).2)⟩

/-- The DN target has the same natural area and smaller area moment. -/
theorem target_measureLT : MeasureLT (dnTarget hD h) D := by
  have hxt : (x, t) ∈ naturalPairs D := mem_naturalPairs.mpr (naturalRel_of_strictRel h.root)
  have huy : (u, y) ∉ (naturalPairs D).erase (x, t) := fun hm =>
    h.not_nat_uy (mem_naturalPairs.mp (Finset.mem_of_mem_erase hm))
  have hpairs : naturalPairs (dnTarget hD h) = insert (u, y) ((naturalPairs D).erase (x, t)) := by
    ext ⟨a, b⟩
    rw [mem_naturalPairs, dnTarget_naturalRel, Finset.mem_insert, Finset.mem_erase,
      mem_naturalPairs]
    unfold dnNatural
    simp only [ne_eq, Prod.mk.injEq]
    tauto
  right
  rw [naturalArea_eq_card, naturalArea_eq_card, areaMoment_eq_sum, areaMoment_eq_sum, hpairs,
    Finset.card_insert_of_notMem huy, Finset.card_erase_of_mem hxt, Finset.sum_insert huy]
  have hpos : 0 < (naturalPairs D).card := Finset.card_pos.mpr ⟨_, hxt⟩
  refine ⟨by lia, ?_⟩
  have hsum := Finset.add_sum_erase (naturalPairs D) (fun p => p.2.val) hxt
  simp only at hsum
  have hyt : y.val < t.val := h.yt
  lia

end DNContact

end

end VerticalStripLLT.Circular.DiagramProof
