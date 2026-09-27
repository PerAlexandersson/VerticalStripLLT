import VerticalStripLLT.Components.GainFeasibility

/-!
# Strict cycle inequalities and scaled integer gains

For `M ≥ card V`, replacing every gain `δ` by `M * δ + 1` converts strict
negativity on nonempty simple cycles into nonpositivity on all closed walks.
The selected quiver retains loops and parallel edge instances.
-/

namespace VerticalStripLLT.Components

section WeightedPaths

variable {V : Type*} [Quiver V]

private theorem scaling_vertices_prefix {a b c : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    p.vertices.Sublist (p.comp q).vertices := by
  induction q with
  | nil => exact List.Sublist.refl _
  | cons q e ih =>
    change p.vertices.Sublist ((p.comp q).cons e).vertices
    rw [Quiver.Path.vertices_cons, List.concat_eq_append]
    exact ih.trans (List.sublist_append_left _ _)

private theorem exists_nodup_path_of_simple_cycles_nonpos
    (weight : ∀ {a b : V}, (a ⟶ b) → ℤ)
    (hsimple : ∀ v (p : Quiver.Path v v),
      0 < p.length → p.vertices.dropLast.Nodup → p.addWeight weight ≤ 0)
    {a b : V} (p : Quiver.Path a b) :
    ∃ q : Quiver.Path a b, q.vertices.Nodup ∧ p.addWeight weight ≤ q.addWeight weight := by
  classical
  induction p with
  | nil => exact ⟨Quiver.Path.nil, by simp, le_rfl⟩
  | @cons b c p e ih =>
    obtain ⟨q, hq, hgain⟩ := ih
    by_cases hmem : c ∈ q.vertices
    · obtain ⟨q₁, q₂, hqeq⟩ := q.exists_eq_comp_of_mem_vertices hmem
      have hprefix : q₁.vertices.Sublist q.vertices := by
        rw [hqeq]
        exact scaling_vertices_prefix q₁ q₂
      have hsuffix : q₂.vertices.Sublist q.vertices := by
        rw [hqeq, Quiver.Path.vertices_comp]
        exact List.sublist_append_right _ _
      have hcycle := hsimple c (q₂.cons e) (by simp)
        (by simpa only [Quiver.Path.vertices_cons, List.concat_eq_append,
          List.dropLast_concat] using
          List.Nodup.sublist hsuffix hq)
      refine ⟨q₁, List.Nodup.sublist hprefix hq, ?_⟩
      have hsum : q.addWeight weight = q₁.addWeight weight + q₂.addWeight weight := by
        rw [hqeq, Quiver.Path.addWeight_comp]
      simp only [Quiver.Path.addWeight_cons] at hcycle ⊢
      lia
    · refine ⟨q.cons e, ?_, ?_⟩
      · rw [Quiver.Path.vertices_cons, List.nodup_concat]
        exact ⟨hmem, hq⟩
      · simp only [Quiver.Path.addWeight_cons]
        lia

private theorem closed_weight_nonpos_of_simple_cycles_nonpos
    (weight : ∀ {a b : V}, (a ⟶ b) → ℤ)
    (hsimple : ∀ v (p : Quiver.Path v v),
      0 < p.length → p.vertices.dropLast.Nodup → p.addWeight weight ≤ 0)
    (v : V) (p : Quiver.Path v v) : p.addWeight weight ≤ 0 := by
  obtain ⟨q, hq, hpq⟩ := exists_nodup_path_of_simple_cycles_nonpos weight hsimple p
  cases q with
  | nil => simpa using hpq
  | cons q e =>
    rw [Quiver.Path.vertices_cons, List.nodup_concat] at hq
    exact (hq.1 q.start_mem_vertices).elim

end WeightedPaths

namespace GainData

variable {V E : Type*} (G : GainData V E)

/-- Number of edge instances traversed by a selected walk. -/
abbrev walkLength {A : Finset E} {u v : V} (p : G.Walk A u v) : ℕ :=
  @Quiver.Path.length V (G.selectedQuiver A) u v p

/-- A nonempty closed walk with no repeated vertex before its final endpoint. -/
def SimpleCycle {A : Finset E} {v : V} (p : G.Walk A v v) : Prop :=
  let : Quiver V := G.selectedQuiver A
  0 < G.walkLength p ∧ p.vertices.dropLast.Nodup

/-- Every simple directed cycle has nonpositive gain. -/
def SimpleCyclesNonpos (A : Finset E) : Prop :=
  ∀ v (p : G.Walk A v v), G.SimpleCycle p → G.walkGain p ≤ 0

/-- Every nonempty simple directed cycle has strictly negative gain. -/
def SimpleCyclesNegative (A : Finset E) : Prop :=
  ∀ v (p : G.Walk A v v), G.SimpleCycle p → G.walkGain p < 0

/-- Simple cycles suffice to test nonpositivity of all directed closed walks. -/
theorem closedWalksNonpos_iff_simpleCyclesNonpos (A : Finset E) :
    G.ClosedWalksNonpos A ↔ G.SimpleCyclesNonpos A := by
  constructor
  · intro h v p _
    exact h v p
  · intro h v p
    let : Quiver V := G.selectedQuiver A
    exact @closed_weight_nonpos_of_simple_cycles_nonpos V (G.selectedQuiver A)
      (fun {_ _} e => G.gain e.val) (fun w q hlen hnodup => h w q ⟨hlen, hnodup⟩) v p

/-- A simple cycle uses at most one edge per vertex. -/
theorem simpleCycle_length_le_card [Fintype V] {A : Finset E} {v : V}
    {p : G.Walk A v v} (hp : G.SimpleCycle p) :
    G.walkLength p ≤ Fintype.card V := by
  let : Quiver V := G.selectedQuiver A
  have hlen := hp.2.length_le_card
  simpa only [walkLength, List.length_dropLast, Quiver.Path.vertices_length, Nat.add_sub_cancel]
    using hlen

/-- Integer scaling that turns strict cycle inequalities into weak ones. -/
abbrev strictScale (M : ℕ) : GainData V E where
  tail := G.tail
  head := G.head
  gain e := (M : ℤ) * G.gain e + 1

/-- Scaling does not alter walks; it adds one unit per edge to the total gain. -/
theorem walkGain_strictScale (M : ℕ) {A : Finset E} {u v : V}
    (p : G.Walk A u v) :
    (G.strictScale M).walkGain p = (M : ℤ) * G.walkGain p + G.walkLength p := by
  let : Quiver V := G.selectedQuiver A
  induction p with
  | nil => simp [walkGain, walkLength]
  | cons p e ih =>
    simp only [walkGain, walkLength, Quiver.Path.addWeight_cons] at ih ⊢
    rw [ih]
    simp only [Quiver.Path.length_cons, Int.natCast_add_one, mul_add]
    lia

/-- The scaling criterion, including loops, parallel edges, and the empty vertex set. -/
theorem closedWalksNonpos_strictScale_iff [Fintype V] (A : Finset E) (M : ℕ)
    (hM : Fintype.card V ≤ M) :
    (G.strictScale M).ClosedWalksNonpos A ↔ G.SimpleCyclesNegative A := by
  constructor
  · intro h v p hp
    have hgain := h v p
    rw [G.walkGain_strictScale M p] at hgain
    have hlen : (0 : ℤ) < G.walkLength p := by exact_mod_cast hp.1
    by_contra hnot
    have hnonneg : 0 ≤ G.walkGain p := by lia
    have hprod := mul_nonneg (Int.natCast_nonneg M) hnonneg
    lia
  · intro h
    apply ((G.strictScale M).closedWalksNonpos_iff_simpleCyclesNonpos A).mpr
    intro v p hp
    have hp' : G.SimpleCycle p := hp
    have hnegative := h v p hp'
    have hlenNat := (G.simpleCycle_length_le_card hp').trans hM
    have hlen : (G.walkLength p : ℤ) ≤ M := by exact_mod_cast hlenNat
    have hgain : G.walkGain p ≤ -1 := by lia
    have hmul := mul_le_mul_of_nonneg_left hgain (Int.natCast_nonneg M)
    rw [G.walkGain_strictScale M p]
    have hneg : (M : ℤ) * (-1) = -(M : ℤ) := mul_neg_one _
    rw [hneg] at hmul
    lia

/-- Strict negativity on simple cycles supplies an actual scaled feasible potential. -/
theorem exists_feasible_strictScale_iff [Fintype V] (A : Finset E) (M : ℕ)
    (hM : Fintype.card V ≤ M) :
    (∃ p : V → ℕ, (G.strictScale M).Feasible A p) ↔ G.SimpleCyclesNegative A := by
  rw [(G.strictScale M).exists_feasible_iff_closedWalksNonpos,
    G.closedWalksNonpos_strictScale_iff A M hM]

end GainData

end VerticalStripLLT.Components
