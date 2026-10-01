import VerticalStripLLT.Components.DiagramProof.Preparation.OrderedSweep

/-! Relation algebra for restoring the exterior after a last-clique replacement. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V : Type*} [LinearOrder V]

/-- The outgoing restoration leaves the prefix and final vertex unchanged. -/
theorem lastClique_restore_inside {S : V → V → Prop} {a c e : V}
    (hSforward : ∀ ⦃u v⦄, S u v → u < v)
    (hSrow : ∀ v, a < v → v ≤ c → ¬ S a v)
    (u v : V) (hu : u ≤ c ∨ u = e) (hv : v ≤ c ∨ v = e) :
    outgoingSweepRelation S a e e u v ↔ S u v := by
  constructor
  · intro h
    rcases h with hnew | hold
    · rcases hnew with ⟨hau, hue, _, hsu⟩
      rcases hu with huc | rfl
      · exact (hSrow u hau huc hsu).elim
      · exact (lt_irrefl _ hue).elim
    · exact hold.1
  · intro hsu
    apply Or.inr
    refine ⟨hsu, ?_⟩
    rintro ⟨rfl, hve⟩
    rcases hv with hvc | rfl
    · exact (hSrow v (hSforward hsu) hvc hsu).elim
    · exact (lt_irrefl _ hve).elim

/-- The outgoing restoration agrees with the original relation outside the core. -/
theorem lastClique_restore_outside {R S : V → V → Prop} {a c e : V}
    (hRforward : ∀ ⦃u v⦄, R u v → u < v)
    (hac : a < c)
    (hout : ∀ u v,
      ¬ ((u ≤ c ∨ u = e) ∧ (v ≤ c ∨ v = e)) →
        (S u v ↔ incomingSweepRelation R a c e u v))
    (hRrow : ∀ v, a < v → v < e → ¬ R a v)
    (u v : V)
    (houtside : ¬ ((u ≤ c ∨ u = e) ∧ (v ≤ c ∨ v = e))) :
    outgoingSweepRelation S a e e u v ↔ R u v := by
  have incoming_eq_of_not_pivot_not_final {x y : V} (hxa : x ≠ a) (hye : y ≠ e) :
      incomingSweepRelation R a c e x y ↔ R x y := by
    rw [incomingSweepRelation_iff]
    constructor
    · rintro (hnew | hold)
      · exact (hxa hnew.2.2.1).elim
      · exact hold.1
    · intro hxy
      exact Or.inr ⟨hxy, fun h => hye h.1⟩
  have incoming_not_to_final {x : V} (hcx : c < x) :
      ¬ incomingSweepRelation R a c e x e := by
    rw [incomingSweepRelation_iff]
    rintro (hnew | hold)
    · exact (lt_irrefl _ hnew.1).elim
    · exact hold.2 ⟨rfl, hcx⟩
  have incoming_from_pivot {x : V} (hxe : x < e)
      (hcx : c < x) :
      incomingSweepRelation R a c e a x ↔ R x e := by
    rw [incomingSweepRelation_iff]
    constructor
    · rintro (hnew | hold)
      · exact hnew.2.2.2
      · exact (hRrow x (hRforward hold.1) hxe hold.1).elim
    · intro hxe'
      exact Or.inl ⟨hxe, hcx, rfl, hxe'⟩
  by_cases hve : v = e
  · subst v
    have hu_core : ¬ (u ≤ c ∨ u = e) := by
      intro hu
      exact houtside ⟨hu, Or.inr rfl⟩
    have hua : u ≠ a := by
      intro hua
      exact hu_core (Or.inl (hua.symm ▸ hac.le))
    have hue : u ≠ e := by
      intro hue
      exact hu_core (Or.inr hue)
    have hu_le : ¬ u ≤ c := fun hle => hu_core (Or.inl hle)
    have hcu : c < u := lt_of_not_ge hu_le
    have hSue : S u e ↔ incomingSweepRelation R a c e u e :=
      hout u e houtside
    rcases lt_or_gt_of_ne hue with hue_lt | he_lt
    · have hSau : S a u ↔ incomingSweepRelation R a c e a u := by
        apply hout
        intro h
        exact hu_core h.2
      have hinau := incoming_from_pivot hue_lt hcu
      have hinue := incoming_not_to_final hcu
      constructor
      · intro h
        rcases h with hnew | hold
        · exact hinau.mp (hSau.mp hnew.2.2.2)
        · exact (hinue (hSue.mp hold.1)).elim
      · intro hue'
        apply Or.inl
        exact ⟨hac.trans hcu, hue_lt, rfl, hSau.mpr (hinau.mpr hue')⟩
    · have hinue := incoming_not_to_final hcu
      constructor
      · intro h
        rcases h with hnew | hold
        · exact (not_lt_of_ge he_lt.le hnew.2.1).elim
        · exact (hinue (hSue.mp hold.1)).elim
      · intro hue'
        exact (not_lt_of_ge he_lt.le (hRforward hue')).elim
  · by_cases hua : u = a
    · subst u
      by_cases hve_lt : v < e
      · have hRav : ¬ R a v := by
          intro hav
          exact (hRrow v (hRforward hav) hve_lt) hav
        constructor
        · intro h
          rcases h with hnew | hold
          · exact (hve hnew.2.2.1).elim
          · exact (hold.2 ⟨rfl, hve_lt⟩).elim
        · intro hav
          exact (hRav hav).elim
      · have hev : e < v := lt_of_le_of_ne (le_of_not_gt hve_lt) (Ne.symm hve)
        have hSuv : S a v ↔ incomingSweepRelation R a c e a v :=
          hout a v houtside
        have hin : incomingSweepRelation R a c e a v ↔ R a v := by
          rw [incomingSweepRelation_iff]
          constructor
          · rintro (hnew | hold)
            · exact (not_lt_of_ge hev.le hnew.1).elim
            · exact hold.1
          · intro hav
            exact Or.inr ⟨hav, fun h => hve h.1⟩
        constructor
        · intro h
          rcases h with hnew | hold
          · exact (hve hnew.2.2.1).elim
          · exact hin.mp (hSuv.mp hold.1)
        · intro hav
          apply Or.inr
          exact ⟨hSuv.mpr (hin.mpr hav), by
            rintro ⟨_, hlt⟩
            exact (not_lt_of_ge hev.le hlt).elim⟩
    · have hSuv : S u v ↔ incomingSweepRelation R a c e u v :=
        hout u v houtside
      have hin := incoming_eq_of_not_pivot_not_final hua hve
      constructor
      · intro h
        rcases h with hnew | hold
        · exact (hve hnew.2.2.1).elim
        · exact hin.mp (hSuv.mp hold.1)
      · intro huv
        apply Or.inr
        exact ⟨hSuv.mpr (hin.mpr huv), fun h => hua h.1⟩

end VerticalStripLLT.Circular.DiagramProof
