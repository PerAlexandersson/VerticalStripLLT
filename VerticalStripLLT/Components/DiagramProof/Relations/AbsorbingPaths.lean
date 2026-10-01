import VerticalStripLLT.Components.DiagramProof.Relations.RelationPaths

/-! Paths cannot return after entering an absorbing union of processed chains. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V : Type*} {R S : V → V → Prop} {U : V → Prop}

/-- Every selected edge starting in the processed union stays there. -/
def Absorbing (R : V → V → Prop) (U : V → Prop) : Prop :=
  ∀ ⦃u v⦄, R u v → U u → U v

theorem Absorbing.reachable (hU : Absorbing R U) {u v : V}
    (h : Relation.ReflTransGen R u v) (hu : U u) : U v := by
  induction h with
  | refl => exact hu
  | tail _ hs ih => exact hU hs ih

theorem Absorbing.not_mem_of_reachable (hU : Absorbing R U) {u v : V}
    (h : Relation.ReflTransGen R u v) (hv : ¬ U v) : ¬ U u :=
  fun hu => hv (hU.reachable h hu)

/-- For a path ending outside an absorbing set, only outside edges matter. -/
theorem reachable_mono_outside_absorbing (hU : Absorbing S U)
    (hmap : ∀ u v, ¬ U u → ¬ U v → S u v → R u v)
    {u v : V} (h : Relation.ReflTransGen S u v) (hv : ¬ U v) :
    Relation.ReflTransGen R u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail w v hp hs ih =>
    have hw : ¬ U w := fun h => hv (hU hs h)
    exact (ih hw).tail (hmap w v hw hv hs)

/-- For a path starting inside an absorbing set, only inside edges matter. -/
theorem reachable_mono_inside_absorbing (hU : Absorbing S U)
    (hmap : ∀ u v, U u → U v → S u v → R u v)
    {u v : V} (h : Relation.ReflTransGen S u v) (hu : U u) :
    Relation.ReflTransGen R u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail w v hp hs ih =>
    have hw := hU.reachable hp hu
    exact ih.tail (hmap w v hw (hU hs hw) hs)

variable [LinearOrder V]

/-- Once a newly processed block is absorbing, added edges into it cannot bypass outside covers. -/
theorem relationCover_of_subrelation_outside_absorbing
    (hU : Absorbing S U) (hmap : ∀ u v, ¬ U u → ¬ U v → S u v → R u v)
    {a b : V} (hab : RelationCover R a b) (hsab : S a b) (hb : ¬ U b) :
    RelationCover S a b := by
  refine ⟨hab.1, Relation.ReflTransGen.single hsab, ?_⟩
  intro w haw hwb hw
  exact hab.2.2 w haw hwb
    ⟨reachable_mono_outside_absorbing hU hmap hw.1 (hU.not_mem_of_reachable hw.2 hb),
      reachable_mono_outside_absorbing hU hmap hw.2 hb⟩

/-- Unchanged internal edges preserve every cover of a previously processed block. -/
theorem relationCover_of_subrelation_inside_absorbing
    (hU : Absorbing S U) (hmap : ∀ u v, U u → U v → S u v → R u v)
    {a b : V} (hab : RelationCover R a b) (hsab : S a b) (ha : U a) :
    RelationCover S a b := by
  refine ⟨hab.1, Relation.ReflTransGen.single hsab, ?_⟩
  intro w haw hwb hw
  exact hab.2.2 w haw hwb
    ⟨reachable_mono_inside_absorbing hU hmap hw.1 ha,
      reachable_mono_inside_absorbing hU hmap hw.2 (hU.reachable hw.1 ha)⟩

/-- The first exit outside the processed union covers even if earlier edges enter that union. -/
theorem relationCover_of_first_outside (hforward : ∀ ⦃u v⦄, R u v → u < v)
    (hU : Absorbing R U) {a b : V} (hab : R a b) (hb : ¬ U b)
    (hfirst : ∀ z, a < z → z < b → ¬ U z → ¬ R a z) : RelationCover R a b := by
  refine ⟨hforward hab, Relation.ReflTransGen.single hab, ?_⟩
  intro w haw hwb hw
  rcases hw.1.cases_head with heq | ⟨z, haz, hzw⟩
  · exact haw.ne heq
  · exact hfirst z (hforward haz) ((reachable_le hforward hzw).trans_lt hwb)
      (hU.not_mem_of_reachable (hzw.trans hw.2) hb) haz

end VerticalStripLLT.Circular.DiagramProof
