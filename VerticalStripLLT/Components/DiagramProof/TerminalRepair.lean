import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! An Aristotle candidate for the terminal-transfer repair, locally checked by the primary. -/

namespace VerticalStripLLT.Circular.DiagramProof.TerminalRepair

open SimpleGraph

variable {V : Type*}

/-- After deleting one pair from a connected graph, every vertex is reachable from
one of the two endpoints of that pair. -/
private lemma sides {G : SimpleGraph V} (hG : G.Connected) (u v : V) (w : V) :
    (G.deleteEdges {s(u, v)}).Reachable u w ∨ (G.deleteEdges {s(u, v)}).Reachable v w := by
  obtain ⟨p⟩ := hG.preconnected w u
  have key : ∀ x z (p : G.Walk x z), z = u →
      (G.deleteEdges {s(u, v)}).Reachable u x ∨ (G.deleteEdges {s(u, v)}).Reachable v x := by
    intro x z p
    induction p with
    | nil => rintro rfl; exact Or.inl Reachable.rfl
    | @cons x y _ h p ih =>
      intro hz
      by_cases hxy : s(x, y) = s(u, v)
      · rcases Sym2.eq_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl Reachable.rfl
        · exact Or.inr Reachable.rfl
      · have hadj : (G.deleteEdges {s(u, v)}).Adj y x := by
          rw [deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_swap]
          exact ⟨h.symm, hxy⟩
        rcases ih hz with h1 | h1
        · exact Or.inl (h1.trans hadj.reachable)
        · exact Or.inr (h1.trans hadj.reachable)
  exact key w u p rfl

/-- If every vertex is reachable from `p` or `q`, and `p`, `q` are linked, the graph
is connected. -/
private lemma conn_of_sides {G : SimpleGraph V} {p q : V}
    (hside : ∀ w, G.Reachable p w ∨ G.Reachable q w) (hpq : G.Reachable p q) :
    G.Connected := by
  have hall : ∀ w, G.Reachable p w := fun w =>
    (hside w).elim id (fun h => hpq.trans h)
  exact (connected_iff G).mpr
    ⟨fun x y => (hall x).symm.trans (hall y), ⟨p⟩⟩

/-- Adding a pair joining the two sides gives a connected graph. -/
private lemma join {G : SimpleGraph V} {p q u v : V}
    (hside : ∀ w, G.Reachable p w ∨ G.Reachable q w)
    (hu : G.Reachable p u) (hv : G.Reachable q v) (huv : u ≠ v) :
    (G ⊔ edge u v).Connected := by
  have hle : G ≤ G ⊔ edge u v := le_sup_left
  have hadj : (G ⊔ edge u v).Adj u v := by
    rw [sup_adj, edge_adj]; exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
  refine conn_of_sides (p := p) (q := q) (fun w => (hside w).imp (·.mono hle) (·.mono hle)) ?_
  exact ((hu.mono hle).trans hadj.reachable).trans (hv.mono hle).symm

/-- Deleting a non-edge does nothing (as a lower bound). -/
private lemma le_deleteEdges_of_not_adj {G : SimpleGraph V} {x y : V} (h : ¬G.Adj x y) :
    G ≤ G.deleteEdges {s(x, y)} := by
  intro v w hvw
  rw [deleteEdges_adj, Set.mem_singleton_iff]
  refine ⟨hvw, fun he => h ?_⟩
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hvw
  · exact hvw.symm

private lemma le_sup_deleteEdges {G B : SimpleGraph V} {x y : V} (hB : B ≤ G) (h : ¬G.Adj x y) :
    B ≤ (B ⊔ edge x y).deleteEdges {s(x, y)} := by
  intro v w hvw
  have := le_deleteEdges_of_not_adj h (hB hvw)
  rw [deleteEdges_adj] at this ⊢
  exact ⟨Or.inl hvw, this.2⟩

private lemma deleteEdges_sup_le {G : SimpleGraph V} {x y : V} {F : Sym2 V} (h : s(x, y) ≠ F) :
    G.deleteEdges {F} ⊔ edge x y ≤ (G ⊔ edge x y).deleteEdges {F} := by
  intro v w hvw
  rw [sup_adj] at hvw
  rw [deleteEdges_adj, sup_adj]
  rcases hvw with hvw | hvw
  · rw [deleteEdges_adj] at hvw
    exact ⟨Or.inl hvw.1, hvw.2⟩
  · refine ⟨Or.inr hvw, ?_⟩
    rw [edge_adj] at hvw
    rcases hvw with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩
    · simpa using h
    · rw [Sym2.eq_swap]; simpa using h

private lemma deleteEdges_le_sup_deleteEdges {G K : SimpleGraph V} {F : Sym2 V} :
    G.deleteEdges {F} ≤ (G ⊔ K).deleteEdges {F} := by
  intro v w hvw
  rw [deleteEdges_adj] at hvw ⊢
  exact ⟨Or.inl hvw.1, hvw.2⟩

private lemma deleteEdges_deleteEdges_le {G : SimpleGraph V} {E F : Sym2 V} :
    (G.deleteEdges {E}).deleteEdges {F} ≤ G.deleteEdges {F} := by
  intro v w hvw
  rw [deleteEdges_adj, deleteEdges_adj] at hvw
  rw [deleteEdges_adj]
  exact ⟨hvw.1.1, hvw.2⟩

private lemma ne_of_not_adj {H : SimpleGraph V} {x y u v : V} (hn : ¬H.Adj x y) (h : H.Adj u v) :
    s(x, y) ≠ s(u, v) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hn h
  · exact hn h.symm

/-- One cut: a graph `J` with two sides (those of `p` and of `q`), containing every edge of
`H` other than `E = s(p,q)` and `F = s(r₁,r₂)`, where `r₁, r₂` lie on the `p`-side.  Then a
non-edge of `H` from the `p`-side to `q` reconnects `J`. -/
private lemma cross {H J : SimpleGraph V} {p q r₁ r₂ : V} {E F : Sym2 V}
    (hE : E = s(p, q)) (hF : F = s(r₁, r₂)) (hr : r₁ ≠ r₂)
    (hside : ∀ w, J.Reachable p w ∨ J.Reachable q w) (hpq : ¬J.Reachable p q)
    (h1 : J.Reachable p r₁) (h2 : J.Reachable p r₂)
    (hJ : ∀ x y, H.Adj x y → s(x, y) ≠ E → s(x, y) ≠ F → J.Adj x y) :
    ∃ u, u ≠ q ∧ ¬H.Adj u q ∧ s(u, q) ≠ E ∧ s(u, q) ≠ F ∧
      (J ⊔ edge u q).Connected := by
  subst hE hF
  obtain ⟨u, hup, hpu⟩ : ∃ u, u ≠ p ∧ J.Reachable p u := by
    by_cases h : r₁ = p
    · exact ⟨r₂, fun h' => hr (h.trans h'.symm), h2⟩
    · exact ⟨r₁, h, h1⟩
  have huq : u ≠ q := by rintro rfl; exact hpq hpu
  have hq1 : q ≠ r₁ := by rintro rfl; exact hpq h1
  have hq2 : q ≠ r₂ := by rintro rfl; exact hpq h2
  have hE' : s(u, q) ≠ s(p, q) := by
    rw [Ne, Sym2.eq_iff]; rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact hup h
    · exact huq h
  have hF' : s(u, q) ≠ s(r₁, r₂) := by
    rw [Ne, Sym2.eq_iff]; rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact hq2 h
    · exact hq1 h
  exact ⟨u, huq, fun hadj => hpq (hpu.trans (hJ u q hadj hE' hF').reachable), hE', hF',
    join hside hpu Reachable.rfl huq⟩

/-- Two cuts: `E = s(p,q)` and `F = s(s,t)` are both bridges of `H`, with `F` on the
`q`-side of `E` and `E` on the `s`-side of `F`.  Then `s(p,t)` crosses both cuts. -/
private lemma twoCut {H : SimpleGraph V} {p q s t : V} {E F : Sym2 V}
    (hE : E = s(p, q))
    (hsideE : ∀ w, (H.deleteEdges {E}).Reachable p w ∨ (H.deleteEdges {E}).Reachable q w)
    (hpq : ¬(H.deleteEdges {E}).Reachable p q)
    (hsideF : ∀ w, (H.deleteEdges {F}).Reachable s w ∨ (H.deleteEdges {F}).Reachable t w)
    (hst : ¬(H.deleteEdges {F}).Reachable s t)
    (hqt : (H.deleteEdges {E}).Reachable q t)
    (hsp : (H.deleteEdges {F}).Reachable s p)
    (hsq : (H.deleteEdges {F}).Reachable s q) :
    p ≠ t ∧ ¬H.Adj p t ∧ ((H.deleteEdges {E}) ⊔ edge p t).Connected ∧
      ((H.deleteEdges {F}) ⊔ edge p t).Connected := by
  have hpt : p ≠ t := by rintro rfl; exact hpq hqt.symm
  have htq : t ≠ q := by rintro rfl; exact hst hsq
  refine ⟨hpt, fun hadj => ?_, join hsideE Reachable.rfl hqt hpt,
    join hsideF hsp Reachable.rfl hpt⟩
  have h0 : (H.deleteEdges {E}).Adj p t := by
    rw [deleteEdges_adj, hE, Set.mem_singleton_iff, Sym2.eq_iff]
    refine ⟨hadj, ?_⟩
    rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact htq h
    · exact hpt h.symm
  exact hpq (h0.reachable.trans hqt.symm)

/-- The repair lemma with the "current base graph" abstracted: `base` is either `H`
(the donor keeps a copy) or `H` with `s(a,b)` deleted. -/
private theorem repair_aux (H : SimpleGraph V) (hH : H.Connected) (a b c d : V)
    (hab : H.Adj a b) (hcd : c ≠ d) (hef : s(a, b) ≠ s(c, d)) (base : SimpleGraph V)
    (hbase : base = H ∨ base = H.deleteEdges {s(a, b)})
    (hfinal : (base ⊔ edge c d).Connected) :
    ((H.deleteEdges {s(c, d)}).Connected ∧ ((H.deleteEdges {s(a, b)}) ⊔ edge c d).Connected) ∨
    ∃ x y : V, x ≠ y ∧ ¬H.Adj x y ∧ s(x, y) ≠ s(a, b) ∧ s(x, y) ≠ s(c, d) ∧
      (H.deleteEdges {s(x, y)}).Connected ∧
      ((H.deleteEdges {s(a, b)}) ⊔ edge x y).Connected ∧
      ((base ⊔ edge x y).deleteEdges {s(c, d)}).Connected ∧
      (((base ⊔ edge x y).deleteEdges {s(x, y)}) ⊔ edge c d).Connected := by
  have hbaseH : base ≤ H := by
    rcases hbase with rfl | rfl
    · exact le_rfl
    · exact deleteEdges_le _
  -- the first and fourth conditions are automatic for an absent pair
  have reduce : ∀ x y, x ≠ y → ¬H.Adj x y → s(x, y) ≠ s(c, d) →
      ((H.deleteEdges {s(a, b)}) ⊔ edge x y).Connected →
      ((base ⊔ edge x y).deleteEdges {s(c, d)}).Connected →
      ∃ x y : V, x ≠ y ∧ ¬H.Adj x y ∧ s(x, y) ≠ s(a, b) ∧ s(x, y) ≠ s(c, d) ∧
        (H.deleteEdges {s(x, y)}).Connected ∧
        ((H.deleteEdges {s(a, b)}) ⊔ edge x y).Connected ∧
        ((base ⊔ edge x y).deleteEdges {s(c, d)}).Connected ∧
        (((base ⊔ edge x y).deleteEdges {s(x, y)}) ⊔ edge c d).Connected := by
    intro x y hxy hn hf h2 h3
    exact ⟨x, y, hxy, hn, ne_of_not_adj hn hab, hf, hH.mono (le_deleteEdges_of_not_adj hn),
      h2, h3, hfinal.mono (sup_le_sup_right (le_sup_deleteEdges hbaseH hn) _)⟩
  set G0 := H.deleteEdges {s(a, b)} with hG0def
  set Hf := H.deleteEdges {s(c, d)} with hHfdef
  have hsE : ∀ w, G0.Reachable a w ∨ G0.Reachable b w := sides hH a b
  have hsF : ∀ w, Hf.Reachable c w ∨ Hf.Reachable d w := sides hH c d
  have habF : Hf.Adj a b := by
    rw [hHfdef, deleteEdges_adj, Set.mem_singleton_iff]; exact ⟨hab, hef⟩
  by_cases hA : Hf.Connected
  · by_cases hB : (G0 ⊔ edge c d).Connected
    · exact Or.inl ⟨hA, hB⟩
    right
    -- only `s(a,b)` is responsible: it is a bridge and `s(c,d)` stays on one side
    have hb : base = H := by
      rcases hbase with h | h
      · exact h
      · exact absurd (h ▸ hfinal) hB
    subst base
    have hab0 : ¬G0.Reachable a b := fun h => hB ((conn_of_sides hsE h).mono le_sup_left)
    have hJ : ∀ x y, H.Adj x y → s(x, y) ≠ s(a, b) → s(x, y) ≠ s(c, d) →
        G0.Adj x y := by
      intro x y h h1 _
      rw [hG0def, deleteEdges_adj, Set.mem_singleton_iff]; exact ⟨h, h1⟩
    have h3 : ∀ u v, ((H ⊔ edge u v).deleteEdges {s(c, d)}).Connected :=
      fun u v => hA.mono deleteEdges_le_sup_deleteEdges
    rcases hsE c with hac | hbc
    · have had : G0.Reachable a d := by
        refine (hsE d).resolve_right fun hbd => hB ?_
        exact join hsE hac hbd hcd
      obtain ⟨u, hub, hn, hfE, hfF, hconn⟩ :=
        cross (H := H) (E := s(a, b)) (F := s(c, d)) rfl rfl hcd hsE hab0 hac had
          (fun x y h h1 h2 => hJ x y h h1 h2)
      exact reduce u b hub hn hfF hconn (h3 u b)
    · have hbd : G0.Reachable b d := by
        refine (hsE d).resolve_left fun had => hB ?_
        rw [edge_comm]; exact join hsE had hbc hcd.symm
      obtain ⟨u, hua, hn, hfE, hfF, hconn⟩ :=
        cross (H := H) (J := G0) (p := b) (q := a) (E := s(a, b)) (F := s(c, d))
          Sym2.eq_swap rfl hcd (fun w => (hsE w).symm) (fun h => hab0 h.symm) hbc hbd
          (fun x y h h1 h2 => hJ x y h h1 h2)
      exact reduce u a hua hn hfF hconn (h3 u a)
  right
  have hcdF : ¬Hf.Reachable c d := fun h => hA (conn_of_sides hsF h)
  have hcdadj : H.Adj c d := by
    by_contra h; exact hA (hH.mono (le_deleteEdges_of_not_adj h))
  have hG0cd : G0.Adj c d := by
    rw [hG0def, deleteEdges_adj, Set.mem_singleton_iff]
    exact ⟨hcdadj, fun h => hef h.symm⟩
  have hsup : G0 ⊔ edge c d ≤ G0 := by
    refine sup_le le_rfl fun v w hvw => ?_
    rw [edge_adj] at hvw
    rcases hvw with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩
    · exact hG0cd
    · exact hG0cd.symm
  by_cases hB : (G0 ⊔ edge c d).Connected
  · -- only `s(c,d)` is responsible: `s(a,b)` is not a bridge
    have hG0 : G0.Connected := hB.mono hsup
    have h2 : ∀ u v, (G0 ⊔ edge u v).Connected := fun u v => hG0.mono le_sup_left
    rcases hbase with hb | hb <;> subst base
    · -- the donor keeps a copy: cut `Hf`
      have hJ : ∀ x y, H.Adj x y → s(x, y) ≠ s(c, d) → s(x, y) ≠ s(a, b) →
          Hf.Adj x y := by
        intro x y h h1 _
        rw [hHfdef, deleteEdges_adj, Set.mem_singleton_iff]; exact ⟨h, h1⟩
      rcases hsF a with hca | hda
      · obtain ⟨u, hud, hn, hfE, hfF, hconn⟩ :=
          cross (H := H) (E := s(c, d)) (F := s(a, b)) rfl rfl hab.ne hsF hcdF hca
            (hca.trans habF.reachable) hJ
        exact reduce u d hud hn hfE (h2 u d) (hconn.mono (deleteEdges_sup_le hfE))
      · obtain ⟨u, huc, hn, hfE, hfF, hconn⟩ :=
          cross (H := H) (J := Hf) (p := d) (q := c) (E := s(c, d)) (F := s(a, b))
            Sym2.eq_swap rfl hab.ne (fun w => (hsF w).symm) (fun h => hcdF h.symm) hda
            (hda.trans habF.reachable) hJ
        exact reduce u c huc hn hfE (h2 u c) (hconn.mono (deleteEdges_sup_le hfE))
    · -- the last donor copy disappears: cut `W = G0 - s(c,d)`
      set W := G0.deleteEdges {s(c, d)} with hWdef
      have hWle : W ≤ Hf := deleteEdges_deleteEdges_le
      have hsW : ∀ w, W.Reachable c w ∨ W.Reachable d w := sides hG0 c d
      have hcdW : ¬W.Reachable c d := fun h => hcdF (h.mono hWle)
      have hJ : ∀ x y, H.Adj x y → s(x, y) ≠ s(c, d) → s(x, y) ≠ s(a, b) →
          W.Adj x y := by
        intro x y h h1 h2
        rw [hWdef, deleteEdges_adj, hG0def, deleteEdges_adj, Set.mem_singleton_iff,
          Set.mem_singleton_iff]
        exact ⟨⟨h, h2⟩, h1⟩
      rcases hsW a with hca | hda
      · have hcb : W.Reachable c b := by
          refine (hsW b).resolve_right fun hdb => hcdF ?_
          exact ((hca.mono hWle).trans habF.reachable).trans (hdb.mono hWle).symm
        obtain ⟨u, hud, hn, hfE, hfF, hconn⟩ :=
          cross (H := H) (E := s(c, d)) (F := s(a, b)) rfl rfl hab.ne hsW hcdW hca hcb hJ
        exact reduce u d hud hn hfE (h2 u d) (hconn.mono (deleteEdges_sup_le hfE))
      · have hdb : W.Reachable d b := by
          refine (hsW b).resolve_left fun hcb => hcdF ?_
          exact (hcb.mono hWle).trans (((hda.mono hWle).trans habF.reachable).symm)
        obtain ⟨u, huc, hn, hfE, hfF, hconn⟩ :=
          cross (H := H) (J := W) (p := d) (q := c) (E := s(c, d)) (F := s(a, b))
            Sym2.eq_swap rfl hab.ne (fun w => (hsW w).symm) (fun h => hcdW h.symm) hda hdb hJ
        exact reduce u c huc hn hfE (h2 u c) (hconn.mono (deleteEdges_sup_le hfE))
  · -- both pairs are bridges: join the two outer components
    have hb : base = H := by
      rcases hbase with h | h
      · exact h
      · exact absurd (h ▸ hfinal) hB
    subst base
    have hab0 : ¬G0.Reachable a b := fun h => hB ((conn_of_sides hsE h).mono le_sup_left)
    have fin : ∀ p t, p ≠ t → ¬H.Adj p t → (G0 ⊔ edge p t).Connected →
        (Hf ⊔ edge p t).Connected → _ := fun p t hpt hn h2 h3' =>
      reduce p t hpt hn (ne_of_not_adj hn hcdadj) h2 (h3'.mono (deleteEdges_sup_le
        (ne_of_not_adj hn hcdadj)))
    have hsE' : ∀ w, G0.Reachable b w ∨ G0.Reachable a w := fun w => (hsE w).symm
    have hsF' : ∀ w, Hf.Reachable d w ∨ Hf.Reachable c w := fun w => (hsF w).symm
    rcases hsE c with hac | hbc <;> rcases hsF a with hca | hda
    · -- `s(c,d)` on the `a`-side, `s(a,b)` on the `c`-side: join `b` to `d`
      obtain ⟨hpt, hn, h2, h3⟩ := twoCut (H := H) (p := b) (q := a) (s := c) (t := d)
        (E := s(a, b)) (F := s(c, d)) Sym2.eq_swap hsE' (fun h => hab0 h.symm) hsF hcdF
        (hac.trans hG0cd.reachable) (hca.trans habF.reachable) hca
      exact fin b d hpt hn h2 h3
    · obtain ⟨hpt, hn, h2, h3⟩ := twoCut (H := H) (p := b) (q := a) (s := d) (t := c)
        (E := s(a, b)) (F := s(c, d)) Sym2.eq_swap hsE' (fun h => hab0 h.symm) hsF'
        (fun h => hcdF h.symm) hac (hda.trans habF.reachable) hda
      exact fin b c hpt hn h2 h3
    · obtain ⟨hpt, hn, h2, h3⟩ := twoCut (H := H) (p := a) (q := b) (s := c) (t := d)
        (E := s(a, b)) (F := s(c, d)) rfl hsE hab0 hsF hcdF
        (hbc.trans hG0cd.reachable) hca (hca.trans habF.reachable)
      exact fin a d hpt hn h2 h3
    · obtain ⟨hpt, hn, h2, h3⟩ := twoCut (H := H) (p := a) (q := b) (s := d) (t := c)
        (E := s(a, b)) (F := s(c, d)) rfl hsE hab0 hsF'
        (fun h => hcdF h.symm) hbc hda (hda.trans habF.reachable)
      exact fin a c hpt hn h2 h3

/-- **One temporary edge repairs a terminal-clique transfer.**

Let `H` be connected, `e = s(a,b)` an edge of `H`, `f = s(c,d)` with `c ≠ d` and `e ≠ f`,
and `final := (if keep then H else H - e) ⊔ edge c d` connected.  Then either the transfer
`e → f` is direct, or there is an absent pair `g = s(x,y)` (different from `e`, `f`) such
that the two transfers `e → g` and `g → f` are both direct. -/
theorem one_temporary_edge_repair (H : SimpleGraph V) (hH : H.Connected) (a b c d : V)
    (hab : H.Adj a b) (hcd : c ≠ d) (hef : s(a, b) ≠ s(c, d)) (keep : Bool)
    (hfinal : ((if keep then H else H.deleteEdges {s(a, b)}) ⊔ edge c d).Connected) :
    ((H.deleteEdges {s(c, d)}).Connected ∧
        ((H.deleteEdges {s(a, b)}) ⊔ edge c d).Connected) ∨
    ∃ x y : V, x ≠ y ∧ ¬H.Adj x y ∧ s(x, y) ≠ s(a, b) ∧ s(x, y) ≠ s(c, d) ∧
      (H.deleteEdges {s(x, y)}).Connected ∧
      ((H.deleteEdges {s(a, b)}) ⊔ edge x y).Connected ∧
      (((if keep then H else H.deleteEdges {s(a, b)}) ⊔ edge x y).deleteEdges
          {s(c, d)}).Connected ∧
      ((((if keep then H else H.deleteEdges {s(a, b)}) ⊔ edge x y).deleteEdges
          {s(x, y)}) ⊔ edge c d).Connected := by
  exact repair_aux H hH a b c d hab hcd hef _ (by cases keep <;> simp) hfinal

end VerticalStripLLT.Circular.DiagramProof.TerminalRepair
