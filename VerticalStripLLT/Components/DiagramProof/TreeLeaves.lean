import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! A finite tree remains a tree after attaching every omitted vertex as a leaf. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {U V : Type*} [Fintype U] [Fintype V]

theorem tree_with_attached_leaves (i : U ↪ V) (j : U)
    (T : SimpleGraph U) (hT : T.IsTree) :
    (SimpleGraph.fromRel (fun x y : V =>
      (∃ u v : U, T.Adj u v ∧ i u = x ∧ i v = y) ∨
      (x ∉ Set.range i ∧ y = i j))).IsTree := by
  set G := SimpleGraph.fromRel (fun x y : V =>
      (∃ u v : U, T.Adj u v ∧ i u = x ∧ i v = y) ∨
      (x ∉ Set.range i ∧ y = i j)) with hG
  have hcore : ∀ {u v : U}, T.Adj u v → G.Adj (i u) (i v) := by
    intro u v h
    rw [hG, SimpleGraph.fromRel_adj]
    exact ⟨fun e => h.ne (i.injective e), Or.inl (Or.inl ⟨u, v, h, rfl, rfl⟩)⟩
  have hleaf : ∀ {x : V}, x ∉ Set.range i → G.Adj x (i j) := by
    intro x hx
    rw [hG, SimpleGraph.fromRel_adj]
    exact ⟨fun e => hx ⟨j, e.symm⟩, Or.inl (Or.inr ⟨hx, rfl⟩)⟩
  let φ : T →g G := ⟨i, hcore⟩
  have hreach : ∀ x, G.Reachable (i j) x := by
    intro x
    by_cases hx : x ∈ Set.range i
    · obtain ⟨u, rfl⟩ := hx
      exact (hT.connected.preconnected j u).map φ
    · exact (hleaf hx).symm.reachable
  have hconn : G.Connected := by
    have : Nonempty V := ⟨i j⟩
    exact SimpleGraph.Connected.mk fun x y => (hreach x).symm.trans (hreach y)
  let f : T.edgeSet ⊕ ((Set.range i)ᶜ : Set V) → G.edgeSet := fun s =>
    match s with
    | Sum.inl e => ⟨e.1.map i, by
        obtain ⟨e, he⟩ := e
        induction e using Sym2.ind with
        | _ a b => exact hcore he⟩
    | Sum.inr x => ⟨s(x.1, i j), hleaf x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro (⟨e, he⟩ | ⟨x, hx⟩) (⟨e', he'⟩ | ⟨y, hy⟩) h
      · have h' : Sym2.map i e = Sym2.map i e' := congrArg Subtype.val h
        have := Sym2.map.injective i.injective h'
        subst this
        rfl
      · have h' : Sym2.map i e = s(y, i j) := congrArg Subtype.val h
        have hmem : y ∈ Sym2.map i e := h' ▸ Sym2.mem_mk_left _ _
        obtain ⟨a, -, rfl⟩ := Sym2.mem_map.mp hmem
        exact absurd ⟨a, rfl⟩ hy
      · have h' : s(x, i j) = Sym2.map i e' := congrArg Subtype.val h
        have hmem : x ∈ Sym2.map i e' := h' ▸ Sym2.mem_mk_left _ _
        obtain ⟨a, -, rfl⟩ := Sym2.mem_map.mp hmem
        exact absurd ⟨a, rfl⟩ hx
      · have h' : s(x, i j) = s(y, i j) := congrArg Subtype.val h
        have := Sym2.congr_left.mp h'
        subst this
        rfl
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ x y =>
        rw [SimpleGraph.mem_edgeSet, hG, SimpleGraph.fromRel_adj] at he
        obtain ⟨_, h⟩ := he
        rcases h with (⟨u, v, huv, rfl, rfl⟩ | ⟨hx, rfl⟩) |
          (⟨u, v, huv, rfl, rfl⟩ | ⟨hy, rfl⟩)
        · exact ⟨Sum.inl ⟨s(u, v), huv⟩, rfl⟩
        · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
        · exact ⟨Sum.inl ⟨s(u, v), huv⟩, by
            simp only [f, Subtype.mk.injEq, Sym2.map_mk]
            exact Sym2.eq_swap⟩
        · exact ⟨Sum.inr ⟨y, hy⟩, by
            apply Subtype.ext
            exact Sym2.eq_swap⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  have hTc := ((SimpleGraph.isTree_iff_connected_and_card).mp hT).2
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_sum, add_right_comm, hTc,
    Nat.card_congr (Equiv.ofInjective i i.injective)]
  exact Set.ncard_add_ncard_compl _

end

end VerticalStripLLT.Circular.DiagramProof
