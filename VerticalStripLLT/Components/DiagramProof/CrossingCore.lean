import VerticalStripLLT.Components.DiagramProof.RelationExchange

/-! The two central crossing flips after the outgoing and incoming obstructions are swept. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V : Type*} [LinearOrder V] {R S : V → V → Prop}

/-- The newly inserted `bc` cannot bypass `bd` when its head cannot reach `d`. -/
theorem relationCover_crossing_first
    (hR : ∀ ⦃u v⦄, R u v → u < v) (hS : ∀ ⦃u v⦄, S u v → u < v)
    {a b c d : V} (hab : a < b) (hbc : b < c)
    (hbd : RelationCover R b d) (hnocd : ¬ Relation.ReflTransGen R c d)
    (hswap : ∀ u v, S u v ↔ exchangeRelation R a b b c u v) :
    RelationCover S b d := by
  have hmap : ∀ u v, S u v → R u v ∨ (u = b ∧ v = c) := by
    intro u v hs
    rcases (hswap u v).mp hs with hnew | ⟨hold, _⟩
    · exact Or.inr hnew
    · exact Or.inl hold
  have hno : ¬ Relation.ReflTransGen S c d := by
    intro hp
    apply hnocd
    apply reachable_mono_on_interval hS (lo := c) (hi := d) ?_ hp le_rfl le_rfl
    intro u v hcu _ hs
    rcases hmap u v hs with hold | ⟨rfl, _⟩
    · exact hold
    · exact (not_le_of_gt hbc hcu).elim
  have hselected : S b d := (hswap b d).mpr (Or.inr
    ⟨rel_of_relationCover hR hbd, fun h => hab.ne h.1.symm⟩)
  refine ⟨hbd.1, Relation.ReflTransGen.single hselected, ?_⟩
  intro w hbw hwd hw
  exact hbd.2.2 w hbw hwd
    ⟨reachable_without_added_edge_to hmap (fun h => hno (h.trans hw.2)) hw.1,
      reachable_without_added_edge_to hmap hno hw.2⟩

theorem exchangeRelation_crossing_chain (R : V → V → Prop) {a b c d : V}
    (hbc : b < c) (hnot : ¬ R b c) (u v : V) :
    exchangeRelation (exchangeRelation R a b b c) b c c d u v ↔
      exchangeRelation R a b c d u v := by
  simp only [exchangeRelation]
  grind

variable {n : ℕ} {D : Diagram n}

/-- Once both sweeps are prepared, two actual flips exchange `ab` for `cd`. -/
theorem exists_preparedCrossing (hforward : Forward D) (θ : Orientation D)
    (a b c d : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hac : Cover θ a c) (hbd : Cover θ b d)
    (hsab : D.edgeData.selected θ.val a b) (hncd : ¬ D.edgeData.selected θ.val c d)
    (hleft : ∀ w, a < w → w < b → ¬ D.edgeData.selected θ.val a w)
    (hright : ∀ w, c < w → w < d → ¬ D.edgeData.selected θ.val w d) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      Cover η a c ∧ Cover η b d ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        exchangeRelation (D.edgeData.selected θ.val) a b c d u v) := by
  have habCover : Cover θ a b :=
    relationCover_of_first_outgoing (fun {_ _} h => θ.selected_lt_of_forward hforward h)
      hsab hleft
  have hnotbc : ¬ D.edgeData.selected θ.val b c := by
    intro h
    exact hac.2.2 b hab hbc
      ⟨Relation.ReflTransGen.single hsab, Relation.ReflTransGen.single h⟩
  have hnocd : ¬ Relation.ReflTransGen (D.edgeData.selected θ.val) c d := by
    apply not_reachable_of_no_incoming
      (fun {_ _} h => θ.selected_lt_of_forward hforward h) hcd
    intro w hcw hwd hw
    rcases lt_or_eq_of_le hcw with hcw | rfl
    · exact hright w hcw hwd hw
    · exact hncd hw
  obtain ⟨ξ, hfirst, hac', hbc', hfirstRel⟩ :=
    exists_outgoingSwap_of_covers hforward θ a b c habCover hac hbc
  have hbd' : Cover ξ b d := relationCover_crossing_first
    (fun {_ _} h => θ.selected_lt_of_forward hforward h)
    (fun {_ _} h => ξ.selected_lt_of_forward hforward h) hab hbc hbd hnocd hfirstRel
  obtain ⟨η, hsecond, hbd'', _, hsecondRel⟩ :=
    exists_outgoingSwap_of_covers hforward ξ b c d hbc' hbd' hcd
  have hac'' : Cover η a c := by
    apply relationCover_of_subrelation_on_interval
      (fun {_ _} h => η.selected_lt_of_forward hforward h) hac'
    · apply (hsecondRel a c).mpr
      exact Or.inr ⟨selected_of_cover hforward hac', fun h => hab.ne h.1⟩
    · intro u v _ hvc hs
      rcases (hsecondRel u v).mp hs with ⟨rfl, rfl⟩ | ⟨hold, _⟩
      · exact (not_le_of_gt hcd hvc).elim
      · exact hold
  refine ⟨η, (Relation.ReflTransGen.single hfirst).tail hsecond, hac'', hbd'', ?_⟩
  intro u v
  exact (hsecondRel u v).trans
    ((exchangeRelation_congr hfirstRel b c c d u v).trans
      (exchangeRelation_crossing_chain _ hbc hnotbc u v))

end VerticalStripLLT.Circular.DiagramProof
