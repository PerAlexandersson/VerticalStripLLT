import Mathlib.Logic.Relation
import Mathlib.Order.Basic

/-! Forward paths stay in their endpoint interval; two-cover exchanges preserve covers. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V : Type*} [LinearOrder V] {R S : V → V → Prop}

/-- The ordinary reachability cover test for an auxiliary forward relation. -/
def RelationCover (R : V → V → Prop) (u v : V) : Prop :=
  u < v ∧ Relation.ReflTransGen R u v ∧
    ∀ w, u < w → w < v →
      ¬ (Relation.ReflTransGen R u w ∧ Relation.ReflTransGen R w v)

theorem reachable_le (hforward : ∀ ⦃u v⦄, R u v → u < v) {u v : V}
    (h : Relation.ReflTransGen R u v) : u ≤ v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact ih.trans (hforward hs).le

/-- Mapping only the edges in the endpoint interval suffices to map a forward path. -/
theorem reachable_mono_on_interval (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {lo hi u v : V}
    (hmap : ∀ x y, lo ≤ x → y ≤ hi → R x y → S x y)
    (h : Relation.ReflTransGen R u v) :
    lo ≤ u → v ≤ hi → Relation.ReflTransGen S u v := by
  induction h with
  | refl => intro _ _; exact Relation.ReflTransGen.refl
  | tail hpath hstep ih =>
    intro hlo hhi
    exact (ih hlo ((hforward hstep).le.trans hhi)).tail
      (hmap _ _ (hlo.trans (reachable_le hforward hpath)) hhi hstep)

theorem rel_of_relationCover (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {u v : V} (h : RelationCover R u v) : R u v := by
  rcases h.2.1.cases_head with heq | ⟨w, huw, hwv⟩
  · exact (h.1.ne heq).elim
  · by_cases hw : w = v
    · exact hw ▸ huw
    · exact (h.2.2 w (hforward huw)
        (lt_of_le_of_ne (reachable_le hforward hwv) hw)
        ⟨Relation.ReflTransGen.single huw, hwv⟩).elim

theorem not_reachable_erase_cover (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {a b : V} (hab : RelationCover R a b) :
    ¬ Relation.ReflTransGen (fun u v => R u v ∧ ¬ (u = a ∧ v = b)) a b := by
  intro h
  rcases h.cases_head with heq | ⟨w, haw, hwb⟩
  · exact hab.1.ne heq
  · have hwb' : Relation.ReflTransGen R w b :=
      Relation.ReflTransGen.mono (fun _ _ hs => hs.1) _ _ hwb
    have hne : w ≠ b := fun heq => haw.2 ⟨rfl, heq⟩
    exact hab.2.2 w (hforward haw.1)
      (lt_of_le_of_ne (reachable_le hforward hwb') hne)
      ⟨Relation.ReflTransGen.single haw.1, hwb'⟩

omit [LinearOrder V] in
/-- A path that cannot reach the added edge's tail never uses that edge. -/
theorem reachable_without_added_edge {a b u v : V}
    (hmap : ∀ x y, S x y → R x y ∨ (x = a ∧ y = b))
    (hno : ¬ Relation.ReflTransGen S u a) (h : Relation.ReflTransGen S u v) :
    Relation.ReflTransGen R u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath hstep ih =>
    rcases hmap _ _ hstep with hs | ⟨rfl, _⟩
    · exact ih.tail hs
    · exact (hno hpath).elim

/-- The target cover tests follow from the two source covers in a forward triangle. -/
theorem relationCover_short_swap (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {a b c : V} (hbc : b < c) (hab : RelationCover R a b) (hac : RelationCover R a c)
    (hswap : ∀ u v, S u v ↔
      (u = b ∧ v = c) ∨ (R u v ∧ ¬ (u = a ∧ v = b))) :
    RelationCover S a c ∧ RelationCover S b c ∧ ¬ Relation.ReflTransGen S a b := by
  have hsforward : ∀ ⦃u v⦄, S u v → u < v := by
    intro u v hs
    rcases (hswap u v).mp hs with ⟨rfl, rfl⟩ | ⟨hr, _⟩
    · exact hbc
    · exact hforward hr
  have hmap : ∀ u v, S u v → R u v ∨ (u = b ∧ v = c) := by
    intro u v hs
    rcases (hswap u v).mp hs with hnew | ⟨hr, _⟩
    · exact Or.inr hnew
    · exact Or.inl hr
  have hnoab : ¬ Relation.ReflTransGen S a b := by
    intro h
    apply not_reachable_erase_cover hforward hab
    apply reachable_mono_on_interval hsforward (lo := a) (hi := b) ?_ h le_rfl le_rfl
    intro u v _ hv hs
    rcases (hswap u v).mp hs with ⟨rfl, rfl⟩ | hold
    · exact (not_le_of_gt hbc hv).elim
    · exact hold
  have hsac : S a c := (hswap a c).mpr (Or.inr
    ⟨rel_of_relationCover hforward hac, fun h => hbc.ne h.2.symm⟩)
  have hsbc : S b c := (hswap b c).mpr (Or.inl ⟨rfl, rfl⟩)
  refine ⟨⟨hac.1, Relation.ReflTransGen.single hsac, ?_⟩,
    ⟨hbc, Relation.ReflTransGen.single hsbc, ?_⟩, hnoab⟩
  · intro w haw hwc hw
    exact hac.2.2 w haw hwc
      ⟨reachable_without_added_edge hmap hnoab hw.1,
        reachable_without_added_edge hmap (fun h => hnoab (hw.1.trans h)) hw.2⟩
  · intro w hbw hwc hw
    have hbwR : Relation.ReflTransGen R b w := by
      apply reachable_mono_on_interval hsforward (lo := b) (hi := w) ?_ hw.1 le_rfl le_rfl
      intro u v _ hv hs
      rcases hmap u v hs with hold | ⟨rfl, rfl⟩
      · exact hold
      · exact (not_le_of_gt hwc hv).elim
    have hwcR : Relation.ReflTransGen R w c :=
      reachable_without_added_edge hmap
        (fun h => not_le_of_gt hbw (reachable_le hsforward h)) hw.2
    exact hac.2.2 w (hab.1.trans hbw) hwc ⟨hab.2.1.trans hbwR, hwcR⟩

end VerticalStripLLT.Circular.DiagramProof
