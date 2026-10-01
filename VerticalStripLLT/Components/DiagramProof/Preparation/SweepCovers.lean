import VerticalStripLLT.Components.DiagramProof.Relations.RelationPaths
import Mathlib.Order.OrderDual

/-! Interval-local cover tests and the two ordered sweep directions. -/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

variable {V : Type*} [LinearOrder V] {R S : V → V → Prop}

/-- A cover reverses when both the vertex order and all arrows are reversed. -/
theorem relationCover_dual (u v : V) :
    RelationCover (V := OrderDual V) (Function.swap R) v u ↔ RelationCover R u v := by
  constructor
  · rintro ⟨huv, hreach, hcover⟩
    refine ⟨huv, Relation.reflTransGen_swap.mp hreach, ?_⟩
    intro w huw hwv hw
    exact hcover w hwv huw
      ⟨Relation.reflTransGen_swap.mpr hw.2, Relation.reflTransGen_swap.mpr hw.1⟩
  · rintro ⟨huv, hreach, hcover⟩
    refine ⟨huv, Relation.reflTransGen_swap.mpr hreach, ?_⟩
    intro w hwv huw hw
    exact hcover w huw hwv
      ⟨Relation.reflTransGen_swap.mp hw.2, Relation.reflTransGen_swap.mp hw.1⟩

/-- Incoming short-edge exchanges follow from the same two-cover lemma in the dual order. -/
theorem relationCover_incoming_swap (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {a b c : V} (hab : a < b) (hbc : RelationCover R b c) (hac : RelationCover R a c)
    (hswap : ∀ u v, S u v ↔
      (u = a ∧ v = b) ∨ (R u v ∧ ¬ (u = b ∧ v = c))) :
    RelationCover S a c ∧ RelationCover S a b ∧ ¬ Relation.ReflTransGen S b c := by
  have hswap' : ∀ u v : OrderDual V, Function.swap S u v ↔
      (u = b ∧ v = a) ∨ (Function.swap R u v ∧ ¬ (u = c ∧ v = b)) := by
    intro u v
    simpa only [Function.swap, and_comm] using hswap v u
  have h := relationCover_short_swap (V := OrderDual V)
    (R := Function.swap R) (S := Function.swap S)
    (fun {u v} hs => hforward (u := v) (v := u) hs) hab
    ((relationCover_dual b c).mpr hbc) ((relationCover_dual a c).mpr hac) hswap'
  exact ⟨(relationCover_dual a c).mp h.1, (relationCover_dual a b).mp h.2.1,
    fun hp => h.2.2 (Relation.reflTransGen_swap.mpr hp)⟩

/-- Paths depend only on edges inside their endpoint interval. -/
theorem reachable_congr_on_interval
    (hR : ∀ ⦃u v⦄, R u v → u < v) (hS : ∀ ⦃u v⦄, S u v → u < v)
    {lo hi u v : V} (hrel : ∀ x y, lo ≤ x → y ≤ hi → (R x y ↔ S x y))
    (hlo : lo ≤ u) (hhi : v ≤ hi) :
    Relation.ReflTransGen R u v ↔ Relation.ReflTransGen S u v :=
  ⟨fun h => reachable_mono_on_interval hR (fun x y hx hy => (hrel x y hx hy).mp) h hlo hhi,
    fun h => reachable_mono_on_interval hS (fun x y hx hy => (hrel x y hx hy).mpr) h hlo hhi⟩

/-- Edges outside an interval cannot change any of its cover tests. -/
theorem relationCover_congr_on_interval
    (hR : ∀ ⦃u v⦄, R u v → u < v) (hS : ∀ ⦃u v⦄, S u v → u < v)
    {lo hi u v : V} (hrel : ∀ x y, lo ≤ x → y ≤ hi → (R x y ↔ S x y))
    (hlo : lo ≤ u) (hhi : v ≤ hi) : RelationCover R u v ↔ RelationCover S u v := by
  have paths {x y : V} (hx : lo ≤ x) (hy : y ≤ hi) :
      Relation.ReflTransGen R x y ↔ Relation.ReflTransGen S x y :=
    reachable_congr_on_interval hR hS hrel hx hy
  constructor
  · rintro ⟨huv, hreach, hcover⟩
    refine ⟨huv, (paths hlo hhi).mp hreach, ?_⟩
    intro w huw hwv hw
    exact hcover w huw hwv
      ⟨(paths hlo (hwv.le.trans hhi)).mpr hw.1,
        (paths (hlo.trans huw.le) hhi).mpr hw.2⟩
  · rintro ⟨huv, hreach, hcover⟩
    refine ⟨huv, (paths hlo hhi).mpr hreach, ?_⟩
    intro w huw hwv hw
    exact hcover w huw hwv
      ⟨(paths hlo (hwv.le.trans hhi)).mp hw.1,
        (paths (hlo.trans huw.le) hhi).mp hw.2⟩

/-- Before the first selected outgoing neighbor, no nontrivial forward path can end. -/
theorem not_reachable_before_first_outgoing (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {a b w : V} (hfirst : ∀ z, a < z → z < b → ¬ R a z)
    (haw : a < w) (hwb : w < b) : ¬ Relation.ReflTransGen R a w := by
  intro h
  rcases h.cases_head with heq | ⟨z, haz, hzw⟩
  · exact haw.ne heq
  · exact hfirst z (hforward haz) ((reachable_le hforward hzw).trans_lt hwb) haz

theorem relationCover_of_first_outgoing (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {a b : V} (hab : R a b) (hfirst : ∀ z, a < z → z < b → ¬ R a z) :
    RelationCover R a b := by
  refine ⟨hforward hab, Relation.ReflTransGen.single hab, ?_⟩
  intro w haw hwb hw
  exact not_reachable_before_first_outgoing hforward hfirst haw hwb hw.1

theorem relationCover_of_last_incoming (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {b c : V} (hbc : R b c) (hlast : ∀ z, b < z → z < c → ¬ R z c) :
    RelationCover R b c := by
  apply (relationCover_dual b c).mp
  exact relationCover_of_first_outgoing (V := OrderDual V)
    (R := Function.swap R) (fun {u v} hs => hforward (u := v) (v := u) hs) hbc
    (fun z hzc hbz => hlast z hbz hzc)

/-- No path reaches an endpoint if every possible final incoming edge is absent. -/
theorem not_reachable_of_no_incoming (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {a b : V} (hab : a < b) (hno : ∀ w, a ≤ w → w < b → ¬ R w b) :
    ¬ Relation.ReflTransGen R a b := by
  intro h
  rcases h.cases_tail with heq | ⟨w, haw, hwb⟩
  · exact hab.ne heq.symm
  · exact hno w (reachable_le hforward haw) (hforward hwb) hwb

omit [LinearOrder V] in
/-- A path ending beyond an unreachable new head never uses the added edge. -/
theorem reachable_without_added_edge_to {a b u v : V}
    (hmap : ∀ x y, S x y → R x y ∨ (x = a ∧ y = b))
    (hno : ¬ Relation.ReflTransGen S b v) (h : Relation.ReflTransGen S u v) :
    Relation.ReflTransGen R u v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hs hp ih =>
    rcases hmap _ _ hs with hr | ⟨rfl, rfl⟩
    · exact ih.head hr
    · exact (hno hp).elim

/-- Deleting interval edges preserves a retained cover. -/
theorem relationCover_of_subrelation_on_interval
    (hS : ∀ ⦃u v⦄, S u v → u < v) {a c : V}
    (hac : RelationCover R a c) (hselected : S a c)
    (hsub : ∀ u v, a ≤ u → v ≤ c → S u v → R u v) : RelationCover S a c := by
  refine ⟨hac.1, Relation.ReflTransGen.single hselected, ?_⟩
  intro w haw hwc hw
  exact hac.2.2 w haw hwc
    ⟨reachable_mono_on_interval hS hsub hw.1 le_rfl hwc.le,
      reachable_mono_on_interval hS hsub hw.2 haw.le le_rfl⟩

end VerticalStripLLT.Circular.DiagramProof
