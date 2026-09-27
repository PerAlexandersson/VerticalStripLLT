import VerticalStripLLT.Components.GainContraction

/-! Balanced potentials and weak connectivity for a directed triangle swap. -/

namespace VerticalStripLLT.Components.GainData

open Classical

noncomputable section

variable {V E : Type*} [DecidableEq E] (G : GainData V E)

variable {e f g : E} {F : Finset E}

variable (he : e ∈ F) (hg : g ∈ F) (heg : e ≠ g)
variable (ht : G.tail e = G.tail g) (hm : G.head e = G.tail f)
variable (hh : G.head f = G.head g)
variable (hgain : G.gain g = G.gain e + G.gain f)

local notation "F'" => insert f (F.erase e)

private theorem mem_F'_g (hg : g ∈ F) (heg : e ≠ g) : g ∈ F' := by
  apply Finset.mem_insert.mpr
  right
  exact Finset.mem_erase.mpr ⟨Ne.symm heg, hg⟩

private theorem mem_F'_f : f ∈ F' := by
  exact Finset.mem_insert.mpr (Or.inl rfl)

include he hg heg ht hm hh hgain in
/-- Replacing the first edge of a gain triangle preserves balanced potentials. -/
theorem balancedPotential_triangle_swap {p : V → ℤ} :
    G.BalancedPotential F p ↔ G.BalancedPotential F' p := by
  constructor
  · intro hp a ha
    rcases Finset.mem_insert.mp ha with haf | ha
    · subst a
      have hg' := hp g hg
      have he' := hp e he
      calc
        p (G.head f) - p (G.tail f) =
            p (G.head g) - p (G.head e) := by rw [hh, ← hm]
        _ = (p (G.head g) - p (G.tail g)) -
            (p (G.head e) - p (G.tail e)) := by rw [ht]; ring
        _ = G.gain g - G.gain e := by rw [hg', he']
        _ = G.gain f := by lia
    · exact hp a (Finset.mem_erase.mp ha).2
  · intro hp a ha
    by_cases hae : a = e
    · subst a
      have hg' := hp g (mem_F'_g (F := F) (e := e) (f := f) (g := g) hg heg)
      have hf' := hp f (mem_F'_f (F := F) (e := e) (f := f))
      calc
        p (G.head e) - p (G.tail e) =
            p (G.tail f) - p (G.tail g) := by rw [hm, ht]
        _ = (p (G.head g) - p (G.tail g)) -
            (p (G.head f) - p (G.tail f)) := by rw [hh]; ring
        _ = G.gain g - G.gain f := by rw [hg', hf']
        _ = G.gain e := by lia
    · apply hp a
      apply Finset.mem_insert.mpr
      right
      exact Finset.mem_erase.mpr ⟨hae, ha⟩

include hg heg ht hm hh in
private theorem selected_rel_forward {u v : V}
    (h : G.selectedRelation F u v) :
    Relation.EqvGen (G.selectedRelation F') u v := by
  rcases h with ⟨a, ha, htail, hhead⟩
  by_cases hae : a = e
  · subst a
    rw [← htail, ← hhead]
    have hge := mem_F'_g (F := F) (e := e) (f := f) (g := g) hg heg
    have hfe := mem_F'_f (F := F) (e := e) (f := f)
    apply Relation.EqvGen.trans _ _ _
    · exact Relation.EqvGen.rel _ _ ⟨g, hge, ht.symm, rfl⟩
    · apply Relation.EqvGen.symm _ _
      exact Relation.EqvGen.rel _ _ ⟨f, hfe, hm.symm, hh⟩
  · exact Relation.EqvGen.rel _ _ ⟨a,
      Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hae, ha⟩)),
      htail, hhead⟩

include he hg ht hm hh in
private theorem selected_rel_backward {u v : V}
    (h : G.selectedRelation F' u v) :
    Relation.EqvGen (G.selectedRelation F) u v := by
  rcases h with ⟨a, ha, htail, hhead⟩
  rcases Finset.mem_insert.mp ha with rfl | ha
  · have he' := he
    have hg' := hg
    rw [← htail, ← hhead]
    apply Relation.EqvGen.trans _ _ _
    · apply Relation.EqvGen.symm _ _
      exact Relation.EqvGen.rel _ _ ⟨e, he', rfl, hm⟩
    · exact Relation.EqvGen.rel _ _ ⟨g, hg', ht.symm, hh.symm⟩
  · have haF := (Finset.mem_erase.mp ha).2
    exact Relation.EqvGen.rel _ _ ⟨a, haF, htail, hhead⟩

include hg heg ht hm hh in
private theorem selected_eqvGen_forward {u v : V}
    (h : Relation.EqvGen (G.selectedRelation F) u v) :
    Relation.EqvGen (G.selectedRelation F') u v := by
  induction h with
  | rel _ _ h => exact selected_rel_forward G hg heg ht hm hh h
  | refl x => exact Relation.EqvGen.refl x
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

include he hg ht hm hh in
private theorem selected_eqvGen_backward {u v : V}
    (h : Relation.EqvGen (G.selectedRelation F') u v) :
    Relation.EqvGen (G.selectedRelation F) u v := by
  induction h with
  | rel _ _ h => exact selected_rel_backward G he hg ht hm hh h
  | refl x => exact Relation.EqvGen.refl x
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

include he hg heg ht hm hh in
/-- Replacing the first edge of a gain triangle preserves weak connectivity. -/
theorem selectedRelation_eqvGen_triangle_swap {u v : V} :
    Relation.EqvGen (G.selectedRelation F) u v ↔
      Relation.EqvGen (G.selectedRelation F') u v := by
  constructor
  · exact selected_eqvGen_forward G hg heg ht hm hh
  · exact selected_eqvGen_backward G he hg ht hm hh

end

end VerticalStripLLT.Components.GainData
