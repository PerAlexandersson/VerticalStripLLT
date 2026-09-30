import VerticalStripLLT.Components.DiagramProof.ParallelPacking
import VerticalStripLLT.Components.DiagramProof.Preparation

/-! Common-cover connectivity when all non-corner copies have one label. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

open Classical

noncomputable section

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

private theorem occupancy_eq_of_single_label {p : Fin n × Fin n}
    {θ η : Orientation D} (hθ : F.Anchor hforward θ) (hη : F.Anchor hforward η)
    (hlabel : ∀ e, e ∉ F.edges → F.GoodEdge hforward e →
      F.copyLabel hforward e = p)
    (hsize : totalSelected θ = totalSelected η) :
    ∀ q, F.occupancy hforward θ q = F.occupancy hforward η q := by
  intro q
  let Aθ := fullSelection θ \ F.edges
  let Aη := fullSelection η \ F.edges
  have hcard : Aθ.card = Aη.card := by
    apply Nat.add_right_cancel
    calc
      Aθ.card + F.edges.card = totalSelected θ := by
        exact Finset.card_sdiff_add_card_eq_card hθ.1
      _ = totalSelected η := hsize
      _ = Aη.card + F.edges.card := by
        symm
        exact Finset.card_sdiff_add_card_eq_card hη.1
  have hdecomp (σ : Orientation D) (hσ : F.Anchor hforward σ) :
      (fullSelection σ).filter (fun e => F.copyLabel hforward e = q) =
        (F.edges.filter (fun e => F.copyLabel hforward e = q)) ∪
          ((fullSelection σ \ F.edges).filter
            (fun e => F.copyLabel hforward e = q)) := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_filter.mp he with ⟨hefull, heq⟩
      by_cases heC : e ∈ F.edges
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨heC, heq⟩))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr
            ⟨Finset.mem_sdiff.mpr ⟨hefull, heC⟩, heq⟩))
    · intro he
      rcases Finset.mem_union.mp he with heC | heA
      · rcases Finset.mem_filter.mp heC with ⟨heC, heq⟩
        exact Finset.mem_filter.mpr ⟨hσ.1 heC, heq⟩
      · exact Finset.mem_filter.mpr
          ⟨(Finset.mem_sdiff.mp (Finset.mem_filter.mp heA).1).1,
            (Finset.mem_filter.mp heA).2⟩
  have hAfilter (σ : Orientation D) (hσ : F.Anchor hforward σ) :
      ((fullSelection σ \ F.edges).filter
        (fun e => F.copyLabel hforward e = q)).card =
        if q = p then (fullSelection σ \ F.edges).card else 0 := by
    by_cases hqp : q = p
    · subst q
      rw [ite_eq_left rfl]
      apply congrArg Finset.card
      ext e
      constructor
      · intro he
        exact (Finset.mem_filter.mp he).1
      · intro he
        have hegood := hσ.2 e (Finset.mem_sdiff.mp he).1
        have heq := hlabel e (Finset.mem_sdiff.mp he).2 hegood
        exact Finset.mem_filter.mpr ⟨he, heq⟩
    · rw [ite_eq_right hqp]
      apply Finset.card_eq_zero.mpr
      ext e
      constructor
      · intro he
        have heA := Finset.mem_filter.mp he
        have hegood := hσ.2 e (Finset.mem_sdiff.mp heA.1).1
        exact (hqp (heA.2.symm.trans (hlabel e
          (Finset.mem_sdiff.mp heA.1).2 hegood))).elim
      · simp
  have hdisj (σ : Orientation D) :
      Disjoint (F.edges.filter (fun e => F.copyLabel hforward e = q))
        ((fullSelection σ \ F.edges).filter
          (fun e => F.copyLabel hforward e = q)) := by
    apply Finset.disjoint_left.mpr
    intro e heC heA
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp heA).1).2
      (Finset.mem_filter.mp heC).1
  rw [occupancy, occupancy, hdecomp θ hθ, hdecomp η hη,
    Finset.card_union_of_disjoint (hdisj θ),
    Finset.card_union_of_disjoint (hdisj η), hAfilter θ hθ, hAfilter η hη]
  by_cases hqp : q = p
  · simp only [ite_eq_left hqp]
    simpa [Aθ, Aη] using congrArg
      (fun k => (F.edges.filter (fun e => F.copyLabel hforward e = q)).card + k)
      hcard
  · simp only [ite_eq_right hqp]

/-- Fixed-size anchors connect when every good non-corner has one copy label. -/
theorem anchors_connected_of_single_label {p : Fin n × Fin n}
    {θ η : Orientation D} (hθ : F.Anchor hforward θ) (hη : F.Anchor hforward η)
    (hlabel : ∀ e, e ∉ F.edges → F.GoodEdge hforward e →
      F.copyLabel hforward e = p)
    (hsize : totalSelected θ = totalSelected η) :
    Relation.ReflTransGen (Flip D) θ η := by
  apply F.anchors_connected_of_occupancy hforward hθ hη
  exact occupancy_eq_of_single_label F hforward hθ hη hlabel hsize

/-- Every good non-corner in a two-terminal family is the sole off-diagonal copy. -/
theorem copyLabel_eq_of_two_terminals {r s : Fin n} (hrs : r ≤ s)
    (hterminal : ∀ v, F.terminal hforward v = r ∨ F.terminal hforward v = s)
    {e : Edge D.area} (he : e ∉ F.edges) (hgood : F.GoodEdge hforward e) :
    F.copyLabel hforward e = (r, s) := by
  change e ∈ F.edges ∨
    F.terminal hforward e.tail < F.terminal hforward e.head at hgood
  have hlt : F.terminal hforward e.tail < F.terminal hforward e.head :=
    hgood.resolve_left he
  rcases hterminal e.tail with ht | ht <;> rcases hterminal e.head with hh | hh
  · rw [ht, hh] at hlt
    exact (lt_irrefl _ hlt).elim
  · simp only [copyLabel, ht, hh]
  · rw [ht, hh] at hlt
    exact (not_lt_of_ge hrs hlt).elim
  · rw [ht, hh] at hlt
    exact (lt_irrefl _ hlt).elim

/-- Two terminal fibres give fixed-size anchor connectivity, including `r = s`. -/
theorem anchors_connected_of_two_terminals {r s : Fin n} (hrs : r ≤ s)
    (hterminal : ∀ v, F.terminal hforward v = r ∨ F.terminal hforward v = s)
    {θ η : Orientation D} (hθ : F.Anchor hforward θ) (hη : F.Anchor hforward η)
    (hsize : totalSelected θ = totalSelected η) :
    Relation.ReflTransGen (Flip D) θ η := by
  apply F.anchors_connected_of_single_label hforward hθ hη (p := (r, s))
    (fun e he hgood => F.copyLabel_eq_of_two_terminals hforward hrs hterminal he hgood)
    hsize

/-- Common-cover states of one size connect in a two-terminal corner family. -/
theorem commonCover_connected_of_two_terminals {r s : Fin n} (hrs : r ≤ s)
    (hterminal : ∀ v, F.terminal hforward v = r ∨ F.terminal hforward v = s)
    {θ η : Orientation D} (hθ : F.CommonCover θ) (hη : F.CommonCover η)
    (hsize : totalSelected θ = totalSelected η) :
    Relation.ReflTransGen (Flip D) θ η := by
  obtain ⟨θ', hpθ, haθ, _⟩ := F.exists_preparation hforward θ hθ
  obtain ⟨η', hpη, haη, _⟩ := F.exists_preparation hforward η hη
  have hsize' : totalSelected θ' = totalSelected η' :=
    (totalSelected_eq_of_reachable hpθ).symm.trans
      (hsize.trans (totalSelected_eq_of_reachable hpη))
  exact hpθ.trans ((F.anchors_connected_of_two_terminals hforward hrs hterminal
    haθ haη hsize').trans (flip_reachable_symm hpη))

end

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
