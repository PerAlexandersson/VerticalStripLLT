import VerticalStripLLT.Components.DiagramProof.CopyPaths

/-! Each unordered pair of corner chains supports at most one auxiliary short-edge path. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- The unordered pair of endpoint chains, in increasing terminal order. -/
noncomputable def chainPair (e : Edge D.area) : Fin n × Fin n :=
  (min (F.terminal hforward e.tail) (F.terminal hforward e.head),
    max (F.terminal hforward e.tail) (F.terminal hforward e.head))

theorem chainPair_of_good (e : Edge D.area)
    (he : F.terminal hforward e.tail < F.terminal hforward e.head) :
    F.chainPair hforward e = (F.terminal hforward e.tail, F.terminal hforward e.head) := by
  simp only [chainPair, min_eq_left he.le, max_eq_right he.le]

theorem chainPair_eq_of_shortLink {e f : Edge D.area} (h : F.ShortLink e f) :
    F.chainPair hforward e = F.chainPair hforward f := by
  obtain ⟨ht, hh⟩ := F.shortLink_terminals hforward h
  simp only [chainPair, ht, hh, min_comm, max_comm]

theorem chainPair_eq_of_shortReach {e f : Edge D.area}
    (h : Relation.ReflTransGen F.ShortLink e f) :
    F.chainPair hforward e = F.chainPair hforward f := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (F.chainPair_eq_of_shortLink hforward hs)

/-- A normal short-edge position is either good already or immediately followed by a good one. -/
theorem exists_good_shortReach (e : Edge D.area) (he : e ∉ F.edges) :
    ∃ g : Edge D.area, F.terminal hforward g.tail < F.terminal hforward g.head ∧
      Relation.ReflTransGen F.ShortLink e g := by
  rcases lt_trichotomy (F.terminal hforward e.tail)
    (F.terminal hforward e.head) with hlt | heq | hgt
  · exact ⟨e, hlt, Relation.ReflTransGen.refl⟩
  · exact (he ((F.terminal_eq_iff_mem hforward e).mp heq)).elim
  · have hne := ((hforward e).trans ((F.le_terminal hforward e.head).trans_lt hgt)).ne
    obtain ⟨g, hlink, _⟩ := F.exists_shortSuccessor hforward e he hne
    have ht := F.shortLink_terminals hforward hlink
    refine ⟨g, ?_, Relation.ReflTransGen.single hlink⟩
    rw [← ht.2, ← ht.1]
    exact hgt

include hforward in
/-- A neighboring pair of good copies comprises two consecutive auxiliary short-edge links. -/
theorem shortReach_of_copyLink {e f : Edge D.area} (h : F.CopyLink e f) :
    Relation.ReflTransGen F.ShortLink e f := by
  obtain ⟨_, g, _, _, _, _, hgt, hgh⟩ :=
    exists_normalShortEdges_of_selected (D := F.diagram) hforward (F.chains hforward)
      e.tail e.head f.tail h.1 (hforward e) h.2.2
  have heg : F.ShortLink e g := ⟨hgt.symm, hgh ▸ h.1⟩
  have hgf : F.ShortLink g f := ⟨hgh, hgt.symm ▸ h.2.1⟩
  exact (Relation.ReflTransGen.single heg).tail hgf

include hforward in
theorem shortReach_of_copyReach {e f : Edge D.area}
    (h : Relation.ReflTransGen F.CopyLink e f) : Relation.ReflTransGen F.ShortLink e f := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.trans (F.shortReach_of_copyLink hforward hs)

theorem chainPair_eq_of_shortConnected {e f : Edge D.area}
    (h : Relation.EqvGen F.ShortLink e f) : F.chainPair hforward e = F.chainPair hforward f := by
  induction h with
  | rel _ _ hs => exact F.chainPair_eq_of_shortLink hforward hs
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Auxiliary path components are exactly the nonempty unordered chain pairs. -/
theorem shortConnected_iff_chainPair_eq (e f : Edge D.area) (he : e ∉ F.edges) (hf : f ∉ F.edges) :
    Relation.EqvGen F.ShortLink e f ↔ F.chainPair hforward e = F.chainPair hforward f := by
  constructor
  · exact F.chainPair_eq_of_shortConnected hforward
  · intro hpair
    obtain ⟨g, hg, heg⟩ := F.exists_good_shortReach hforward e he
    obtain ⟨k, hk, hfk⟩ := F.exists_good_shortReach hforward f hf
    have hgk : F.chainPair hforward g = F.chainPair hforward k :=
      (F.chainPair_eq_of_shortReach hforward heg).symm.trans
        (hpair.trans (F.chainPair_eq_of_shortReach hforward hfk))
    rw [F.chainPair_of_good hforward g hg, F.chainPair_of_good hforward k hk] at hgk
    have hends := Prod.mk.inj hgk
    have hmid : Relation.EqvGen F.ShortLink g k := by
      rcases le_total g.tail k.tail with hle | hle
      · exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
          (F.shortReach_of_copyReach hforward
            (F.copy_reachable_of_tail_le hforward g k hg hends.1 hends.2 hle))
      · apply Relation.EqvGen.symm
        exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
          (F.shortReach_of_copyReach hforward
            (F.copy_reachable_of_tail_le hforward k g hk hends.1.symm hends.2.symm hle))
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ heg)
      (Relation.EqvGen.trans _ _ _ hmid
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ hfk)))

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
