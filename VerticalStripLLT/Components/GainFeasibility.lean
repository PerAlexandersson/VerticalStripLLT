import VerticalStripLLT.Components.GainPotential
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Ring.Int

/-! Feasible integer gain potentials from nonpositive directed closed walks. -/

namespace VerticalStripLLT.Components

section WeightedPaths

variable {V : Type*} [Quiver V]

private theorem path_vertices_sublist_comp {a b c : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    p.vertices.Sublist (p.comp q).vertices := by
  induction q with
  | nil => exact List.Sublist.refl _
  | cons q e ih =>
    change p.vertices.Sublist ((p.comp q).cons e).vertices
    rw [Quiver.Path.vertices_cons, List.concat_eq_append]
    exact ih.trans (List.sublist_append_left _ _)

/-- Delete repeated-vertex closed segments without decreasing the weight. -/
private theorem exists_nodup_path_weight_ge
    (weight : ∀ {a b : V}, (a ⟶ b) → ℤ)
    (hclosed : ∀ v (p : Quiver.Path v v), p.addWeight weight ≤ 0)
    {a b : V} (p : Quiver.Path a b) :
    ∃ q : Quiver.Path a b, q.vertices.Nodup ∧ p.addWeight weight ≤ q.addWeight weight := by
  classical
  induction p with
  | nil => exact ⟨Quiver.Path.nil, by simp, le_rfl⟩
  | @cons b c p e ih =>
    obtain ⟨q, hq, hgain⟩ := ih
    by_cases hmem : c ∈ q.vertices
    · obtain ⟨q₁, q₂, hqeq⟩ := q.exists_eq_comp_of_mem_vertices hmem
      have hcycle := hclosed c (q₂.cons e)
      have hsub : q₁.vertices.Sublist q.vertices := by
        rw [hqeq]
        exact path_vertices_sublist_comp q₁ q₂
      refine ⟨q₁, List.Nodup.sublist hsub hq, ?_⟩
      have hsum : q.addWeight weight = q₁.addWeight weight + q₂.addWeight weight := by
        rw [hqeq, Quiver.Path.addWeight_comp]
      simp only [Quiver.Path.addWeight_cons] at hcycle ⊢
      lia
    · refine ⟨q.cons e, ?_, ?_⟩
      · rw [Quiver.Path.vertices_cons, List.nodup_concat]
        exact ⟨hmem, hq⟩
      · simp only [Quiver.Path.addWeight_cons]
        lia

private theorem path_weight_le_length_mul
    (weight : ∀ {a b : V}, (a ⟶ b) → ℤ) (M : ℤ)
    (hedge : ∀ {a b : V} (e : a ⟶ b), weight e ≤ M)
    {a b : V} (p : Quiver.Path a b) :
    p.addWeight weight ≤ (p.length : ℤ) * M := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simp only [Quiver.Path.addWeight_cons, Quiver.Path.length_cons,
      Int.natCast_add_one, add_mul, one_mul]
    exact add_le_add ih (hedge e)

/-- A uniform gain bound follows by erasing nonpositive cycles, not by enumerating walks. -/
private theorem path_weight_le_card_mul [Fintype V]
    (weight : ∀ {a b : V}, (a ⟶ b) → ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hedge : ∀ {a b : V} (e : a ⟶ b), weight e ≤ M)
    (hclosed : ∀ v (p : Quiver.Path v v), p.addWeight weight ≤ 0)
    {a b : V} (p : Quiver.Path a b) :
    p.addWeight weight ≤ (Fintype.card V : ℤ) * M := by
  obtain ⟨q, hq, hpq⟩ := exists_nodup_path_weight_ge weight hclosed p
  have hlen : q.length ≤ Fintype.card V := by
    have hv := hq.length_le_card
    rw [Quiver.Path.vertices_length] at hv
    lia
  have hlen' : (q.length : ℤ) ≤ Fintype.card V := by exact_mod_cast hlen
  exact hpq.trans ((path_weight_le_length_mul weight M hedge q).trans
    (mul_le_mul_of_nonneg_right hlen' hM))

end WeightedPaths

namespace GainData

noncomputable section

variable {V E : Type*} (G : GainData V E)

/-- The selected multiquiver retains each original edge instance. -/
abbrev selectedQuiver (A : Finset E) : Quiver V where
  Hom u v := {e : E // e ∈ A ∧ G.tail e = u ∧ G.head e = v}

/-- Directed selected walks, including empty walks and walks using parallel edges. -/
abbrev Walk (A : Finset E) (u v : V) := @Quiver.Path V (G.selectedQuiver A) u v

/-- The sum of the original integer gains along a selected walk. -/
def walkGain {A : Finset E} {u v : V} (p : G.Walk A u v) : ℤ :=
  @Quiver.Path.addWeight V (G.selectedQuiver A) ℤ inferInstance
    (fun {_ _} e => G.gain e.val) u v p

/-- Every directed closed walk has nonpositive total gain. -/
def ClosedWalksNonpos (A : Finset E) : Prop :=
  ∀ v (p : G.Walk A v v), G.walkGain p ≤ 0

/-- A feasible potential bounds the gain of every selected walk. -/
theorem walkGain_le_potential {A : Finset E} {p : V → ℕ}
    (hp : G.Feasible A p) {u v : V} (q : G.Walk A u v) :
    (p u : ℤ) + G.walkGain q ≤ p v := by
  let : Quiver V := G.selectedQuiver A
  induction q with
  | nil => simp [walkGain]
  | @cons b c q e ih =>
    have he := hp e.val e.property.1
    rw [e.property.2.1, e.property.2.2] at he
    simpa only [walkGain, Quiver.Path.addWeight_cons, add_assoc] using
      (add_le_add ih (le_refl (G.gain e.val))).trans he

/-- Feasibility excludes positive directed closed walks. -/
theorem closedWalksNonpos_of_feasible {A : Finset E} {p : V → ℕ}
    (hp : G.Feasible A p) : G.ClosedWalksNonpos A := by
  intro v q
  have h := G.walkGain_le_potential hp q
  lia

/-- Nonpositive directed closed walks yield an actual nonnegative integer potential.

The supremum is over nonnegative attained gains. Empty walks supply zero;
cycle deletion gives a uniform finite bound, and `Nat.sSup_mem` supplies a
maximizing walk whenever an edge constraint is checked. -/
theorem exists_feasible_of_closedWalksNonpos [Fintype V] (A : Finset E)
    (hA : G.ClosedWalksNonpos A) : ∃ p : V → ℕ, G.Feasible A p := by
  classical
  let : Quiver V := G.selectedQuiver A
  let weight : ∀ {u v : V}, (u ⟶ v) → ℤ := fun {_ _} e => G.gain e.val
  let M : ℕ := A.sup fun e => (G.gain e).toNat
  let B : ℕ := Fintype.card V * M
  have hedge : ∀ {u v : V} (e : u ⟶ v), weight e ≤ (M : ℤ) := by
    intro u v e
    have he : (G.gain e.val).toNat ≤ M :=
      Finset.le_sup (s := A) (f := fun e : E => (G.gain e).toNat) e.property.1
    exact Int.toNat_le.mp he
  have hclosed : ∀ v (q : Quiver.Path v v), q.addWeight weight ≤ 0 := by
    intro v q
    simpa only [walkGain, weight] using hA v q
  have hbound : ∀ {u v : V} (q : Quiver.Path u v), q.addWeight weight ≤ (B : ℤ) := by
    intro u v q
    have hb := path_weight_le_card_mul weight (M : ℤ) (Int.natCast_nonneg _) hedge hclosed q
    simpa only [B, Int.natCast_mul] using hb
  let values (v : V) : Set ℕ :=
    {k | ∃ (u : V) (q : Quiver.Path u v), q.addWeight weight = (k : ℤ)}
  have hnonempty (v : V) : (values v).Nonempty :=
    ⟨0, v, Quiver.Path.nil, by simp⟩
  have hbounded (v : V) : BddAbove (values v) := by
    refine ⟨B, ?_⟩
    rintro k ⟨u, q, hk⟩
    have hb := hbound q
    rw [hk] at hb
    exact_mod_cast hb
  let p : V → ℕ := fun v => sSup (values v)
  refine ⟨p, ?_⟩
  intro e he
  have hattained := Nat.sSup_mem (hnonempty (G.tail e)) (hbounded (G.tail e))
  obtain ⟨u, q, hq⟩ := hattained
  change q.addWeight weight = (p (G.tail e) : ℤ) at hq
  let arrow : G.tail e ⟶ G.head e := ⟨e, he, rfl, rfl⟩
  let total : ℤ := (p (G.tail e) : ℤ) + G.gain e
  by_cases htotal : 0 ≤ total
  · have hmem : total.toNat ∈ values (G.head e) := by
      refine ⟨u, q.cons arrow, ?_⟩
      rw [Quiver.Path.addWeight_cons]
      change q.addWeight weight + G.gain e = (total.toNat : ℤ)
      rw [hq]
      exact (Int.toNat_of_nonneg htotal).symm
    have hle : total.toNat ≤ p (G.head e) := le_csSup (hbounded (G.head e)) hmem
    have hle' : (total.toNat : ℤ) ≤ p (G.head e) := by exact_mod_cast hle
    rw [Int.toNat_of_nonneg htotal] at hle'
    exact hle'
  · change total ≤ (p (G.head e) : ℤ)
    have hh : (0 : ℤ) ≤ p (G.head e) := Int.natCast_nonneg _
    lia

/-- Difference constraints are feasible exactly when no directed closed walk has positive gain. -/
theorem exists_feasible_iff_closedWalksNonpos [Fintype V] (A : Finset E) :
    (∃ p : V → ℕ, G.Feasible A p) ↔ G.ClosedWalksNonpos A := by
  constructor
  · rintro ⟨p, hp⟩
    exact G.closedWalksNonpos_of_feasible hp
  · exact G.exists_feasible_of_closedWalksNonpos A

/-- The previously defined least potential is feasible under the closed-walk condition. -/
theorem potential_feasible_of_closedWalksNonpos [Fintype V] (A : Finset E)
    (hA : G.ClosedWalksNonpos A) : G.Feasible A (G.potential A) :=
  G.potential_feasible (G.exists_feasible_of_closedWalksNonpos A hA)

end

end GainData

end VerticalStripLLT.Components
