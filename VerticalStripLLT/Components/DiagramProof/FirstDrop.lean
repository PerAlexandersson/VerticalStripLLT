import VerticalStripLLT.Components.DiagramProof.ComponentIsolation
import VerticalStripLLT.Components.DiagramProof.InitialPathUniqueness
import VerticalStripLLT.Components.IntervalDiagram

/-!
# The first strict area drop

Write `b_j` for the least natural predecessor of `j` (or `j` itself) and
`a_j = j - b_j` for the area. Let `t` be the first index with `a_(t+1) < a_t`,
using `a_(k+1) = 0`. In a connected diagram which is not a path, `a_t ≥ 2`. Put
`x = b_t` and `y = x + 1`. Then `xt` is a maximal corner, no natural edge from
`y` or earlier ends after `t`, and either `b_y = b_x` (an NN-type contact) or
`b_y = b_x + 1` (a DN-type contact, with incoming corner `b_x x`).

In a saturated diagram we unmark the corner ending at `y`, if any; the same
whole component is then at an eligible NN or forward DN contact.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k : ℕ} {D : Diagram (k + 1)} (hD : Forward D)

/-- The least natural predecessor of `j`, or `j` itself. -/
def bnd (D : Diagram (k + 1)) (j : Fin (k + 1)) : Fin (k + 1) :=
  Diagram.intervalLeft (naturalRel D) j

include hD in
theorem naturalRel_iff_bnd (u j : Fin (k + 1)) : naturalRel D u j ↔ bnd D j ≤ u ∧ u < j :=
  Diagram.rel_iff_intervalLeft (naturalRel D) (fun h => naturalRel_forward hD h)
    (fun h huv hvw => naturalRel_interval hD h huv hvw)

include hD in
theorem bnd_mono {i j : Fin (k + 1)} (h : i ≤ j) : bnd D i ≤ bnd D j :=
  Diagram.intervalLeft_monotone (naturalRel D)
    (fun h huv hvw => naturalRel_interval hD h huv hvw) h

theorem bnd_le (j : Fin (k + 1)) : bnd D j ≤ j := Diagram.intervalLeft_le _ j

/-- Every adjacent natural edge is present. -/
def AdjacentEdges (D : Diagram (k + 1)) : Prop :=
  ∀ u v : Fin (k + 1), v.val = u.val + 1 → naturalRel D u v

theorem InitialPathBlock.adjacentEdges {b : ℕ} (h : InitialPathBlock D b) :
    AdjacentEdges D := by
  intro u v huv
  by_cases hu : u.val < b
  · exact h.2.2 u v hu huv
  · exact h.2.1 u v (le_of_not_gt hu) (by rw [Fin.lt_def]; lia) (by lia)

theorem AdjacentEdges.connected (h : AdjacentEdges D) :
    ∀ u v, Relation.EqvGen (naturalRel D) u v := by
  have hzero : ∀ j (hj : j < k + 1),
      Relation.EqvGen (naturalRel D) ⟨0, Nat.succ_pos k⟩ ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero => intro hj; exact Relation.EqvGen.refl _
    | succ j ih =>
      intro hj
      exact Relation.EqvGen.trans _ _ _ (ih (by lia))
        (Relation.EqvGen.rel _ _ (h ⟨j, by lia⟩ ⟨j + 1, hj⟩ rfl))
  intro u v
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hzero u.val u.isLt))
    (hzero v.val v.isLt)

include hD in
theorem bnd_lt_of_adjacent (hadj : AdjacentEdges D) (j : Fin (k + 1)) (hj : 0 < j.val) :
    bnd D j < j := by
  have := (naturalRel_iff_bnd hD ⟨j.val - 1, by lia⟩ j).mp (hadj _ _ (by simp; lia))
  exact this.1.trans_lt this.2

/-! ### The first drop -/

/-- The data produced by the first strict area drop. -/
structure FirstDropData (D : Diagram (k + 1)) (x y t : Fin (k + 1)) : Prop where
  succ : y.val = x.val + 1
  yt : y < t
  bnd_t : bnd D t = x
  gap : ∀ p q, naturalRel D p q → t < q → y < p
  split : bnd D y = bnd D x ∨ (bnd D y).val = (bnd D x).val + 1

include hD in
theorem exists_firstDrop (hadj : AdjacentEdges D)
    (hnp : ∃ u v : Fin (k + 1), naturalRel D u v ∧ u.val + 2 ≤ v.val) :
    ∃ x y t : Fin (k + 1), FirstDropData D x y t := by
  let bN : ℕ → ℕ := fun j => if h : j < k + 1 then (bnd D ⟨j, h⟩).val else 0
  have hbN (j : Fin (k + 1)) : bN j.val = (bnd D j).val := dite_eq_left j.isLt
  have hbN' (j : ℕ) (h : j < k + 1) : bN j = (bnd D ⟨j, h⟩).val := dite_eq_left h
  let P : ℕ → Prop := fun j => j < k + 1 ∧ (j = k ∨ bN j + 2 ≤ bN (j + 1))
  have hP : ∃ j, P j := ⟨k, by lia, Or.inl rfl⟩
  let tN := Nat.find hP
  have htP : P tN := Nat.find_spec hP
  have hbefore : ∀ i < tN, ¬ P i := fun i hi => Nat.find_min hP hi
  have htlt : tN < k + 1 := htP.1
  let t : Fin (k + 1) := ⟨tN, htlt⟩
  -- The boundary grows by at most one before `t`.
  have hstep : ∀ i, i < tN → bN (i + 1) ≤ bN i + 1 := by
    intro i hi
    have := hbefore i hi
    simp only [P, not_and, not_or] at this
    have hik : i < k := by lia
    have := (this (by lia)).2
    lia
  -- The area is nondecreasing up to `t`.
  have hmono' : ∀ d j, tN - j = d → j ≤ tN → j - bN j ≤ tN - bN tN := by
    intro d
    induction d with
    | zero =>
      intro j h hj
      have : j = tN := by lia
      rw [this]
    | succ d ih =>
      intro j h hj
      have h1 := ih (j + 1) (by lia) (by lia)
      have h2 := hstep j (by lia)
      have hbj : bN j ≤ j := by
        rw [hbN' j (by lia)]
        exact bnd_le _
      lia
  have hmono : ∀ j, j ≤ tN → j - bN j ≤ tN - bN tN := fun j hj => hmono' _ j rfl hj
  have hbt : bN tN ≤ tN := by rw [hbN' tN htlt]; exact bnd_le t
  -- The root has length at least two.
  have hlen : bN tN + 2 ≤ tN := by
    rcases htP.2 with htk | hdrop
    · obtain ⟨u, v, huv, hgap⟩ := hnp
      have hbv := (naturalRel_iff_bnd hD u v).mp huv
      have hvb : bN v.val + 2 ≤ v.val := by
        rw [hbN]
        have : (bnd D v).val ≤ u.val := hbv.1
        lia
      have := hmono v.val (by have := v.isLt; lia)
      lia
    · have htk : tN < k := by
        by_contra hk
        have : tN = k := by lia
        have h1 : bN (tN + 1) = 0 := by simp [bN, this]
        have h2 : 0 < tN := by lia
        lia
      have hadjt := bnd_lt_of_adjacent hD hadj ⟨tN + 1, by lia⟩ (by simp)
      have : bN (tN + 1) ≤ tN := by
        rw [hbN' (tN + 1) (by lia)]
        have : (bnd D ⟨tN + 1, by lia⟩).val < tN + 1 := hadjt
        lia
      lia
  let x : Fin (k + 1) := bnd D t
  have hx : x.val = bN tN := (hbN t).symm
  let y : Fin (k + 1) := ⟨x.val + 1, by lia⟩
  refine ⟨x, y, t, rfl, ?_, rfl, ?_, ?_⟩
  · change x.val + 1 < tN
    lia
  · intro p q hpq htq
    have htk : tN < k := by have := q.isLt; have : tN < q.val := htq; lia
    have hdrop : bN tN + 2 ≤ bN (tN + 1) := by
      rcases htP.2 with h | h
      · lia
      · exact h
    have hq := (naturalRel_iff_bnd hD p q).mp hpq
    have hmono' := bnd_mono hD (show (⟨tN + 1, by lia⟩ : Fin (k + 1)) ≤ q from by
      rw [Fin.le_def]; have : tN < q.val := htq; simp; lia)
    have h1 : bN (tN + 1) ≤ (bnd D q).val := by rw [hbN' (tN + 1) (by lia)]; exact hmono'
    have h2 : (bnd D q).val ≤ p.val := hq.1
    change x.val + 1 < p.val
    lia
  · have hxy : x ≤ y := by
      change x.val ≤ x.val + 1
      lia
    have hle := bnd_mono hD hxy
    have hst := hstep x.val (by lia)
    rw [hbN x, show x.val + 1 = y.val from rfl, hbN y] at hst
    have hle' : (bnd D x).val ≤ (bnd D y).val := hle
    rcases Nat.lt_or_ge (bnd D x).val (bnd D y).val with h | h
    · exact Or.inr (by lia)
    · exact Or.inl (Fin.ext (by lia))

/-! ### The eligible contact after unmarking the corner at `y` -/

include hD in
theorem isCorner_iff_maximalPair (e : Edge D.area) :
    IsCorner e ↔ MaximalPair (naturalRel D) e.tail e.head := by
  constructor
  · exact maximalPair_of_isCorner hD
  · intro h
    apply (isCorner_iff_maximal hD e).mpr
    intro f hft hfh
    obtain ⟨h1, h2⟩ := h.2 f.tail f.head ⟨f, rfl, rfl⟩ hft hfh
    exact D.endpointEmbedding.injective (Prod.ext h1 h2)

namespace FirstDropData

variable {x y t : Fin (k + 1)} (h : FirstDropData D x y t)

include h hD

omit hD in
theorem xy_lt : x < y := by rw [Fin.lt_def, h.succ]; lia

theorem root_maximal : MaximalPair (naturalRel D) x t := by
  refine ⟨(naturalRel_iff_bnd hD x t).mpr ⟨h.bnd_t.le, h.xy_lt.trans h.yt⟩, ?_⟩
  intro p q hpq hpx htq
  have hq : q = t := by
    by_contra hne
    have := h.gap p q hpq (lt_of_le_of_ne htq (Ne.symm hne))
    exact absurd (hpx.trans h.xy_lt.le) (not_le_of_gt this)
  rw [hq] at hpq ⊢
  have := ((naturalRel_iff_bnd hD p t).mp hpq).1
  rw [h.bnd_t] at this
  exact ⟨le_antisymm hpx this, rfl⟩

theorem tail_x {b : Fin (k + 1)} (hb : MaximalPair (naturalRel D) x b) : b = t := by
  have hxb := naturalRel_forward hD hb.1
  rcases lt_trichotomy b t with hbt | rfl | hbt
  · exact (hb.2 x t (h.root_maximal hD).1 le_rfl hbt.le).2.symm
  · rfl
  · exact absurd (h.gap x b hb.1 hbt) (not_lt_of_gt h.xy_lt)

theorem no_tail_y {b : Fin (k + 1)} (hb : MaximalPair (naturalRel D) y b) : False := by
  have hbt : b ≤ t := by
    by_contra hbt
    exact absurd (h.gap y b hb.1 (lt_of_not_ge hbt)) (lt_irrefl y)
  exact h.xy_lt.ne (hb.2 x t (h.root_maximal hD).1 h.xy_lt.le hbt).1

/-- In the NN-type case no corner ends at `x`. -/
theorem no_head_x (hsplit : bnd D y = bnd D x) {a : Fin (k + 1)}
    (ha : MaximalPair (naturalRel D) a x) : False := by
  have hax := (naturalRel_iff_bnd hD a x).mp ha.1
  have hay : naturalRel D a y :=
    (naturalRel_iff_bnd hD a y).mpr ⟨hsplit ▸ hax.1, hax.2.trans h.xy_lt⟩
  exact h.xy_lt.ne' (ha.2 a y hay le_rfl h.xy_lt.le).2

theorem incoming_lt (hadj : AdjacentEdges D) (hsplit : (bnd D y).val = (bnd D x).val + 1) :
    bnd D x < x := by
  have hxy := (naturalRel_iff_bnd hD x y).mp (hadj x y h.succ)
  rw [Fin.lt_def]
  have : (bnd D y).val ≤ x.val := hxy.1
  lia

theorem incoming_maximal (hadj : AdjacentEdges D)
    (hsplit : (bnd D y).val = (bnd D x).val + 1) :
    MaximalPair (naturalRel D) (bnd D x) x := by
  refine ⟨(naturalRel_iff_bnd hD _ x).mpr ⟨le_rfl, h.incoming_lt hD hadj hsplit⟩, ?_⟩
  intro p q hpq hpu hxq
  rcases lt_or_eq_of_le hxq with hxq | rfl
  · exfalso
    have hyq : y ≤ q := by rw [Fin.le_def, h.succ]; exact hxq
    have h1 := bnd_mono hD hyq
    have h2 := ((naturalRel_iff_bnd hD p q).mp hpq).1
    have : (bnd D y).val ≤ p.val := h1.trans h2
    have : p.val ≤ (bnd D x).val := hpu
    lia
  · exact ⟨le_antisymm hpu ((naturalRel_iff_bnd hD p _).mp hpq).1, rfl⟩

theorem head_x (hadj : AdjacentEdges D) (hsplit : (bnd D y).val = (bnd D x).val + 1)
    {a : Fin (k + 1)} (ha : MaximalPair (naturalRel D) a x) : a = bnd D x := by
  have hax := (naturalRel_iff_bnd hD a x).mp ha.1
  exact (ha.2 _ x (h.incoming_maximal hD hadj hsplit).1 hax.1 le_rfl).1.symm

end FirstDropData

/-- Unmark the strict pairs ending at `y`. -/
def unmarkAt (y : Fin (k + 1)) : Diagram (k + 1) :=
  ofRelations (naturalRel D) (fun a b => strictRel D a b ∧ b ≠ y) (ordinaryRelation_naturalRel hD)
    (fun _ _ h => maximalPair_of_strictRel hD h.1) D.area.positive

theorem unmarkAt_forward (y : Fin (k + 1)) : Forward (unmarkAt hD y) :=
  ofRelations_forward _ _ _ _ _

theorem unmarkAt_naturalRel (y a b : Fin (k + 1)) :
    naturalRel (unmarkAt hD y) a b ↔ naturalRel D a b := ofRelations_naturalRel ..

theorem unmarkAt_strictRel (y a b : Fin (k + 1)) :
    strictRel (unmarkAt hD y) a b ↔ strictRel D a b ∧ b ≠ y := ofRelations_strictRel ..

include hD in
/-- A witness transports along a corresponding state of a diagram with the same
natural relation. -/
theorem hasCommonWitness_of_corresponds {E : Diagram (k + 1)} (hE : Forward E)
    (hnat : ∀ a b, naturalRel D a b ↔ naturalRel E a b) {θ : Orientation D}
    {θ' : Orientation E} (h : Corresponds (Equiv.refl _) θ θ') (hθ : HasCommonWitness θ) :
    HasCommonWitness θ' := by
  obtain ⟨η, hη, hcη, hccη⟩ := hθ
  obtain ⟨η', hp, hc⟩ := h.reachable hD hE (mem_flipComponent_iff.mp hη)
  refine ⟨η', mem_flipComponent_iff.mpr hp, fun a b => ?_, fun e he => ?_⟩
  · exact (hc.weakReach_iff a b).mpr (hcη a b)
  · have heC := (isCorner_iff_maximalPair hE e).mp (Finset.mem_filter.mp he).2
    obtain ⟨f, hft, hfh⟩ := (hnat e.tail e.head).mpr heC.1
    have hfC : IsCorner f := by
      rw [isCorner_iff_maximalPair hD, hft, hfh]
      exact ⟨(hnat _ _).mpr heC.1, fun p q hpq => heC.2 p q ((hnat p q).mp hpq)⟩
    have := hccη f (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfC⟩)
    rw [hft, hfh] at this
    exact (hc.cover_iff e.tail e.head).mpr this

/-- **First-drop certificate.** In a saturated diagram consisting of an initial path
and a block without articulation, which is not a path, the connected common-cover
component is certified by smaller whole components. -/
theorem certifies_firstDrop {b : ℕ} (hblock : InitialPathBlock D b)
    (hsat : ∀ s t, MaximalPair (naturalRel D) s t → strictRel D s t)
    (hnp : ∃ u v : Fin (k + 1), naturalRel D u v ∧ u.val + 2 ≤ v.val)
    (θ : Orientation D) (hθ : HasCommonWitness θ) : ∃ c : Cert k, Certifies ⟨D, hD, θ⟩ c := by
  have hadj := hblock.adjacentEdges
  obtain ⟨x, y, t, hd⟩ := exists_firstDrop hD hadj hnp
  let DN := unmarkAt hD y
  have hDN := unmarkAt_forward hD y
  have hnat : ∀ a b, naturalRel D a b ↔ naturalRel DN a b := fun a b =>
    (unmarkAt_naturalRel hD y a b).symm
  obtain ⟨θN, hc⟩ := exists_corresponds_refl hDN θ
    (fun a b hab => (hnat a b).mp (naturalRel_of_selected hab))
    (fun a b hab => selected_of_strictRel θ ((unmarkAt_strictRel hD y a b).mp hab).1)
  have hθN := hasCommonWitness_of_corresponds hD hDN hnat hc hθ
  have hblockN : InitialPathBlock DN b := by
    refine ⟨fun u v h => hblock.1 u v ((hnat u v).mpr h), fun u v h1 h2 h3 =>
      (hnat u v).mp (hblock.2.1 u v h1 h2 h3), fun u v h1 h2 => (hnat u v).mp
        (hblock.2.2 u v h1 h2)⟩
  have hconnN : ∀ a b, Relation.EqvGen (naturalRel DN) a b := by
    intro a b
    exact Relation.EqvGen.mono (fun u v huv => (hnat u v).mp huv) _ _ (hadj.connected a b)
  have huniqN := commonCoverUnique_of_initialPathBlock b hDN hblockN
  have hstrictN (a b' : Fin (k + 1)) : strictRel DN a b' ↔ strictRel D a b' ∧ b' ≠ y :=
    unmarkAt_strictRel hD y a b'
  have hyt : t ≠ y := hd.yt.ne'
  have hxy : x ≠ y := (hd.xy_lt).ne
  rcases hd.split with hsplit | hsplit
  · -- NN-type contact.
    have hNN : NNContact DN x y t := by
      refine ⟨hd.succ, hd.yt, (hstrictN x t).mpr ⟨hsat _ _ (hd.root_maximal hD), hyt⟩,
        fun p q hpq => hd.gap p q ((hnat p q).mpr hpq), ?_, (hnat x y).mp (hadj x y hd.succ),
        ?_, ?_, ?_, ?_⟩
      · intro p hp
        rw [← hnat, ← hnat, naturalRel_iff_bnd hD, naturalRel_iff_bnd hD, hsplit]
        exact ⟨fun h' => ⟨h'.1, h'.2.trans (hd.xy_lt)⟩, fun h' => ⟨h'.1, hp⟩⟩
      · intro b' hb'
        exact hd.tail_x hD (maximalPair_of_strictRel hD ((hstrictN x b').mp hb').1)
      · intro b' hb'
        exact hd.no_tail_y hD (maximalPair_of_strictRel hD ((hstrictN y b').mp hb').1)
      · intro a ha
        exact hd.no_head_x hD hsplit (maximalPair_of_strictRel hD ((hstrictN a x).mp ha).1)
      · intro a ha
        exact ((hstrictN a y).mp ha).2 rfl
    obtain ⟨c, hcert⟩ := certifies_nn hDN hconnN huniqN θN hθN hNN
    exact ⟨c, certifies_of_corresponds hD hDN hc hnat hcert⟩
  · -- DN-type contact.
    have hux := hd.incoming_lt hD hadj hsplit
    have hDNc : DNContact DN (bnd D x) x y t := by
      refine ⟨hd.succ, hux, hd.yt, (hstrictN x t).mpr ⟨hsat _ _ (hd.root_maximal hD), hyt⟩,
        (hstrictN _ x).mpr ⟨hsat _ _ (hd.incoming_maximal hD hadj hsplit), hxy⟩,
        fun p q hpq => hd.gap p q ((hnat p q).mpr hpq), ?_, (hnat x y).mp (hadj x y hd.succ),
        ?_, ?_, ?_, ?_⟩
      · intro p hp
        rw [← hnat, ← hnat, naturalRel_iff_bnd hD, naturalRel_iff_bnd hD]
        constructor
        · rintro ⟨h1, -⟩
          refine ⟨⟨?_, hp⟩, ?_⟩
          · rw [Fin.le_def]; have : (bnd D y).val ≤ p.val := h1; lia
          · intro he
            rw [he, Fin.le_def] at h1
            lia
        · rintro ⟨⟨h1, -⟩, hne⟩
          refine ⟨?_, hp.trans (hd.xy_lt)⟩
          rw [Fin.le_def, hsplit]
          have : (bnd D x).val ≤ p.val := h1
          have : (bnd D x).val ≠ p.val := fun he => hne (Fin.ext he).symm
          lia
      · intro b' hb'
        exact hd.tail_x hD (maximalPair_of_strictRel hD ((hstrictN x b').mp hb').1)
      · intro b' hb'
        exact hd.no_tail_y hD (maximalPair_of_strictRel hD ((hstrictN y b').mp hb').1)
      · intro a ha
        exact hd.head_x hD hadj hsplit (maximalPair_of_strictRel hD ((hstrictN a x).mp ha).1)
      · intro a ha
        exact ((hstrictN a y).mp ha).2 rfl
    obtain ⟨c, hcert⟩ := certifies_dn hDN hconnN huniqN θN hθN hDNc
    exact ⟨c, certifies_of_corresponds hD hDN hc hnat hcert⟩

end

end VerticalStripLLT.Circular.DiagramProof
