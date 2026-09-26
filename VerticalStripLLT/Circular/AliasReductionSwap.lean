import VerticalStripLLT.Circular.AliasReductionContacts
import VerticalStripLLT.Circular.AdjacentSwap
import VerticalStripLLT.Circular.FirstBounceStrictSwap

set_option backward.isDefEq.respectTransparency false

/-! The simultaneous periodic swap of the contact pairs and the target diagram. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem residue_sub_one_eq_iff (z w : ℤ) :
    D.residue (z - 1) = D.residue w ↔ D.residue z = D.residue (w + 1) := by
  rw [D.residue_eq_iff_mod_sub_zero, D.residue_eq_iff_mod_sub_zero,
    show z - 1 - w = z - (w + 1) by ring]

theorem residue_succ_eq_iff (z w : ℤ) :
    D.residue (z + 1) = D.residue (w + 1) ↔ D.residue z = D.residue w := by
  rw [D.residue_eq_iff_mod_sub_zero, D.residue_eq_iff_mod_sub_zero,
    show z + 1 - (w + 1) = z - w by ring]

end Diagram

namespace AliasContacts

variable {n : ℕ} {D : Diagram n} (K : AliasContacts D)

/-- Residues of the lower contacts. -/
def p (j : ℕ) : Fin n := D.residue (K.P j)

/-- Residues of the upper contacts. -/
def q (j : ℕ) : Fin n := D.residue (K.P j + 1)

/-- Integer lifts of lower contacts. -/
def L : Set ℤ := {z | ∃ j < K.r, D.residue z = K.p j}

/-- The simultaneous swap of every lifted contact pair. -/
noncomputable def σ (z : ℤ) : ℤ := adjacentSwap K.L z

theorem mem_L_iff (z : ℤ) : z ∈ K.L ↔ ∃ j < K.r, D.residue z = K.p j := Iff.rfl

theorem sub_one_mem_L_iff (z : ℤ) : z - 1 ∈ K.L ↔ ∃ j < K.r, D.residue z = K.q j := by
  simp only [mem_L_iff, p, q, D.residue_sub_one_eq_iff]

theorem L_sep : ∀ z ∈ K.L, z + 1 ∉ K.L := by
  rintro z ⟨j, hj, hz⟩ ⟨i, hi, hz1⟩
  have : D.residue (z + 1) = K.q j := by
    unfold q; rw [D.residue_succ_eq_iff]; exact hz
  exact K.nePQ i j hi hj (hz1.symm.trans this)

theorem L_per : ∀ x k : ℤ, x ∈ K.L ↔ x + (n : ℤ) * k ∈ K.L := by
  intro x k
  simp only [mem_L_iff, D.residue_add_period]

theorem σ_translate (z k : ℤ) : K.σ (z + (n : ℤ) * k) = K.σ z + (n : ℤ) * k :=
  adjacentSwap_translate K.L n z k K.L_per

theorem σ_involutive : Function.Involutive K.σ := adjacentSwap_involutive K.L K.L_sep

@[simp] theorem σ_σ (z : ℤ) : K.σ (K.σ z) = z := K.σ_involutive z

theorem σ_of_mem {z : ℤ} (h : z ∈ K.L) : K.σ z = z + 1 := by
  unfold σ adjacentSwap; rw [ite_eq_left h]

theorem σ_of_sub_mem {z : ℤ} (h : z - 1 ∈ K.L) : K.σ z = z - 1 := by
  have hz : z ∉ K.L := by
    intro hz
    exact K.L_sep (z - 1) h (by simpa using hz)
  unfold σ adjacentSwap; rw [ite_eq_right hz, ite_eq_left h]

theorem σ_of_not {z : ℤ} (h : z ∉ K.L) (h' : z - 1 ∉ K.L) : K.σ z = z := by
  unfold σ adjacentSwap; rw [ite_eq_right h, ite_eq_right h']

theorem σ_eq_iff (u w : ℤ) : K.σ u = w ↔ u = K.σ w := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

theorem σ_injective : Function.Injective K.σ := K.σ_involutive.injective

theorem threshold {c : ℤ} (hc : c - 1 ∉ K.L) (u : ℤ) : c ≤ u ↔ c ≤ K.σ u :=
  adjacentSwap_threshold_iff K.L c u hc

theorem S1 {c d : ℤ} (hc : c ∈ K.L) (hd : d - 1 ∉ K.L) (u : ℤ) :
    (c + 2 ≤ u ∧ u < d) ↔ (c + 2 ≤ K.σ u ∧ K.σ u < d) := by
  have h1 : c + 2 - 1 ∉ K.L := by
    rw [show c + 2 - 1 = c + 1 by ring]; exact K.L_sep c hc
  have t1 := K.threshold h1 u
  have t2 := K.threshold hd u
  constructor
  · rintro ⟨a, b⟩
    exact ⟨t1.mp a, lt_of_not_ge fun h => (not_le.mpr b) (t2.mpr h)⟩
  · rintro ⟨a, b⟩
    exact ⟨t1.mpr a, lt_of_not_ge fun h => (not_le.mpr b) (t2.mp h)⟩

theorem S2 {c d : ℤ} (hc : c ∈ K.L) (hd : d - 1 ∉ K.L) (hcd : c + 1 < d) (u : ℤ) :
    (c ≤ u ∧ u < d ∧ u ≠ c + 1) ↔ (c + 1 ≤ K.σ u ∧ K.σ u < d) := by
  have hσc : K.σ c = c + 1 := K.σ_of_mem hc
  by_cases huc : u = c
  · subst huc
    rw [hσc]
    constructor
    · intro _; exact ⟨le_rfl, hcd⟩
    · intro _; exact ⟨le_rfl, by lia, by lia⟩
  by_cases huc1 : u = c + 1
  · subst huc1
    have : K.σ (c + 1) = c := by rw [K.σ_eq_iff, hσc]
    rw [this]
    constructor
    · rintro ⟨_, _, h⟩; exact absurd rfl h
    · rintro ⟨h, _⟩; lia
  have hσ1 : K.σ u ≠ c := by
    intro h; apply huc1; rw [K.σ_eq_iff] at h; rw [h, hσc]
  have hσ2 : K.σ u ≠ c + 1 := by
    intro h; apply huc; rw [K.σ_eq_iff] at h; rw [h, ← hσc, K.σ_σ]
  have := K.S1 hc hd u
  constructor
  · rintro ⟨a, b, _⟩
    have := this.mp ⟨by lia, b⟩
    exact ⟨by lia, this.2⟩
  · rintro ⟨a, b⟩
    have := this.mpr ⟨by lia, b⟩
    exact ⟨by lia, this.2, huc1⟩

theorem P_mem_L (j : ℕ) (hj : j < K.r) : K.P j ∈ K.L := ⟨j, hj, rfl⟩

theorem β_mem_L : K.β ∈ K.L := ⟨K.r - 1, by have := K.two_le; lia, K.res_β⟩

theorem P_sub_one_not_mem_L (j : ℕ) (hj : j < K.r) : K.P j - 1 ∉ K.L := by
  rw [sub_one_mem_L_iff]
  rintro ⟨i, hi, h⟩
  exact K.nePQ j i hj hi h

theorem P_add_one_not_mem_L (j : ℕ) (hj : j < K.r) : K.P j + 1 ∉ K.L :=
  K.L_sep _ (K.P_mem_L j hj)

theorem σ_P (j : ℕ) (hj : j < K.r) : K.σ (K.P j) = K.P j + 1 := K.σ_of_mem (K.P_mem_L j hj)

theorem σ_P1 (j : ℕ) (hj : j < K.r) : K.σ (K.P j + 1) = K.P j := by
  rw [K.σ_eq_iff, K.σ_P j hj]

theorem σ_β : K.σ K.β = K.β + 1 := K.σ_of_mem K.β_mem_L

theorem σ_β1 : K.σ (K.β + 1) = K.β := by rw [K.σ_eq_iff, K.σ_β]

/-! Residue distinctness in index form. -/

theorem p_inj {i j : ℕ} (hi : i < K.r) (hj : j < K.r) (h : K.p i = K.p j) : i = j :=
  K.injP i j hi hj h

theorem q_inj {i j : ℕ} (hi : i < K.r) (hj : j < K.r) (h : K.q i = K.q j) : i = j :=
  K.injQ i j hi hj h

theorem p_ne_q {i j : ℕ} (hi : i < K.r) (hj : j < K.r) : K.p i ≠ K.q j := K.nePQ i j hi hj

theorem r_pos : 0 < K.r := by have := K.two_le; lia

theorem last_lt : K.r - 1 < K.r := by have := K.two_le; lia

/-! The root strict edge and the target diagram. -/

noncomputable def root : Edge D.area := Classical.choose K.strict_t

theorem root_mem : K.root ∈ D.strict := (Classical.choose_spec K.strict_t).1

theorem root_head : K.root.head = D.residue K.t := (Classical.choose_spec K.strict_t).2

theorem root_head_eq_q0 : K.root.head = K.q 0 := by rw [K.root_head, K.res_t]; rfl

theorem root_tail : K.root.tail = K.p (K.r - 1) := by
  have h := D.residue_tail_of_length (u := D.boundary K.t) K.root_head (by
    rw [(D.strict_corner K.root K.root_mem).1, K.root_head, Diagram.boundary]; ring)
  rw [h, K.bt]; rfl

theorem root_next_tail : D.area.next K.root.tail = K.q (K.r - 1) := by
  rw [K.root_tail]; unfold p q; rw [D.residue_succ]

theorem hi : D.area.next (K.p 0) = K.root.head := by
  rw [K.root_head_eq_q0]; unfold p q; rw [D.residue_succ]

theorem area_p0_int : (D.area.area (K.p 0) : ℤ) = K.P 0 - K.β := by
  unfold β Diagram.boundary p; ring

theorem area_q0_int : (D.area.area (K.q 0) : ℤ) = K.P 0 + 1 - K.β := by
  have h := K.b0
  unfold Diagram.boundary at h
  unfold β Diagram.boundary q
  lia

theorem harea : D.area.area K.root.head = D.area.area (K.p 0) + 1 := by
  rw [K.root_head_eq_q0]
  have h1 := K.area_p0_int
  have h2 := K.area_q0_int
  lia

theorem hlen : 3 ≤ K.root.length.val := by
  rw [(D.strict_corner K.root K.root_mem).1, K.root_head]; exact K.area_t

theorem hgap : D.area.area (D.area.next K.root.head) < D.area.area K.root.head := by
  have h := K.gap_t
  rw [K.root_head]
  unfold Diagram.boundary at h
  rw [D.residue_succ] at h
  lia

theorem hheads : ∀ g ∈ D.strict, g.head ≠ K.p 0 := by
  intro g hg hh
  exact K.notStrict0 ⟨g, hg, hh⟩

/-- The valid alias target supplied by the prefix. -/
noncomputable def target : Diagram n :=
  D.aliasTarget (K.p 0) K.root K.root_mem K.hi K.harea K.hlen K.hgap K.hheads

theorem p0_ne_q0 : K.p 0 ≠ K.q 0 := K.p_ne_q K.r_pos K.r_pos

theorem target_area (v : Fin n) : K.target.area.area v =
    Function.update (Function.update D.area.area K.root.head
      (D.area.area K.root.head - 2)) (K.p 0) (D.area.area (K.p 0) - 1) v := by
  unfold target
  rw [D.aliasTarget_area]

theorem target_area_p0 : K.target.area.area (K.p 0) = D.area.area (K.p 0) - 1 := by
  rw [K.target_area, Function.update_self]

theorem target_area_q0 : K.target.area.area (K.q 0) = D.area.area (K.q 0) - 2 := by
  rw [K.target_area, Function.update_of_ne (Ne.symm K.p0_ne_q0), K.root_head_eq_q0,
    Function.update_self]

theorem target_area_other (v : Fin n) (h0 : v ≠ K.p 0) (h1 : v ≠ K.q 0) :
    K.target.area.area v = D.area.area v := by
  rw [K.target_area, Function.update_of_ne h0, K.root_head_eq_q0, Function.update_of_ne h1]

theorem target_residue : K.target.residue = D.residue := D.residue_congr_diagram K.target

theorem target_boundary_p0 {z : ℤ} (hz : D.residue z = K.p 0) :
    K.target.boundary z = D.boundary z + 1 := by
  have h := K.area_p0_int
  have hb := K.β_add_two_le
  unfold Diagram.boundary
  rw [K.target_residue, hz, K.target_area_p0]
  have : 1 ≤ D.area.area (K.p 0) := by lia
  push_cast [this]
  ring

theorem target_boundary_q0 {z : ℤ} (hz : D.residue z = K.q 0) :
    K.target.boundary z = D.boundary z + 2 := by
  have h := K.area_q0_int
  have hb := K.β_add_two_le
  unfold Diagram.boundary
  rw [K.target_residue, hz, K.target_area_q0]
  have : 2 ≤ D.area.area (K.q 0) := by lia
  push_cast [this]
  ring

theorem target_boundary_other {z : ℤ} (h0 : D.residue z ≠ K.p 0) (h1 : D.residue z ≠ K.q 0) :
    K.target.boundary z = D.boundary z := by
  unfold Diagram.boundary
  rw [K.target_residue, K.target_area_other _ h0 h1]

theorem target_boundary_add_period (z k : ℤ) :
    K.target.boundary (z + (n : ℤ) * k) = K.target.boundary z + (n : ℤ) * k :=
  K.target.boundary_add_period z k

theorem target_strictEdges : K.target.pairGraph.strictEdges =
    insert (K.q (K.r - 1), K.p 0)
      (D.pairGraph.strictEdges.erase (K.p (K.r - 1), K.q 0)) := by
  unfold target
  rw [D.aliasTarget_pairGraph_strictEdges, K.root_next_tail, K.root_tail, K.root_head_eq_q0]

end AliasContacts

namespace Diagram

variable {n : ℕ} (D : Diagram n)

theorem strictAt_iff_pair (z : ℤ) :
    D.strictAt z ↔ ∃ a, (a, D.residue z) ∈ D.pairGraph.strictEdges := by
  constructor
  · rintro ⟨e, he, hh⟩
    exact ⟨e.tail, (D.mem_pairGraph_strict_iff _).mpr ⟨e, he, by rw [hh]⟩⟩
  · rintro ⟨a, ha⟩
    obtain ⟨e, he, hp⟩ := (D.mem_pairGraph_strict_iff _).mp ha
    exact ⟨e, he, congrArg Prod.snd hp⟩

end Diagram

namespace AliasContacts

variable {n : ℕ} {D : Diagram n} (K : AliasContacts D)

theorem target_strictAt_iff (z : ℤ) :
    K.target.strictAt z ↔ D.residue z = K.p 0 ∨ (D.strictAt z ∧ D.residue z ≠ K.q 0) := by
  rw [K.target.strictAt_iff_pair, K.target_residue, K.target_strictEdges, D.strictAt_iff_pair]
  constructor
  · rintro ⟨a, ha⟩
    rcases Finset.mem_insert.mp ha with h | h
    · left; exact (congrArg Prod.snd h)
    · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp h
      right
      refine ⟨⟨a, hmem⟩, ?_⟩
      intro hz
      apply hne
      obtain ⟨e, he, hp⟩ := (D.mem_pairGraph_strict_iff _).mp hmem
      have hh : e.head = K.root.head := by
        rw [K.root_head_eq_q0, ← hz]; exact congrArg Prod.snd hp
      have := D.strict_edge_eq_of_head_eq he K.root_mem hh
      subst this
      rw [← hp, K.root_tail, K.root_head_eq_q0]
  · rintro (h | ⟨⟨a, ha⟩, hne⟩)
    · exact ⟨K.q (K.r - 1), Finset.mem_insert.mpr (Or.inl (by rw [h]))⟩
    · refine ⟨a, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨?_, ha⟩)⟩
      intro h
      exact hne (congrArg Prod.snd h)

end AliasContacts

end VerticalStripLLT.Circular
