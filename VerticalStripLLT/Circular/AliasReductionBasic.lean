import VerticalStripLLT.Circular.ForcedColoring
import VerticalStripLLT.Circular.ForcedOrientation
import VerticalStripLLT.Circular.BoundaryEdges
import VerticalStripLLT.Circular.BoundaryRow
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-! Generic finite-set tools: forced-edge erasure for coloring and orientation sums,
relabelling of pair graphs, and a lifted description of selected steps. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace PairGraph

variable {n : ℕ}

theorem coloringLLT_erase_forced_set {m : ℕ} (G : PairGraph n)
    (F : Finset (Fin n × Fin n)) (hF : F ⊆ G.normalEdges)
    (hpath : ∀ e ∈ F, Relation.TransGen (fun x y => (x, y) ∈ G.strictEdges) e.1 e.2) :
    G.coloringLLT m = MvPolynomial.C Polynomial.X ^ F.card *
      (⟨G.normalEdges \ F, G.strictEdges⟩ : PairGraph n).coloringLLT m := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    have hF' : F ⊆ G.normalEdges := (Finset.subset_insert _ _).trans hF
    rw [ih hF' (fun e he => hpath e (Finset.mem_insert_of_mem he))]
    have hmem : a ∈ (⟨G.normalEdges \ F, G.strictEdges⟩ : PairGraph n).normalEdges :=
      Finset.mem_sdiff.mpr ⟨hF (Finset.mem_insert_self _ _), ha⟩
    rw [PairGraph.coloringLLT_eraseNormal_forced _ a hmem
      (hpath a (Finset.mem_insert_self _ _))]
    rw [Finset.card_insert_of_notMem ha, pow_succ, mul_assoc]
    congr 2
    simp only [eraseNormal, Finset.sdiff_insert]

theorem coloringLLT_erase_descent_set {m : ℕ} (G : PairGraph n)
    (F : Finset (Fin n × Fin n))
    (hpath : ∀ e ∈ F, Relation.TransGen (fun x y => (x, y) ∈ G.strictEdges) e.2 e.1) :
    G.coloringLLT m =
      (⟨G.normalEdges \ F, G.strictEdges⟩ : PairGraph n).coloringLLT m := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    rw [ih (fun e he => hpath e (Finset.mem_insert_of_mem he))]
    rw [PairGraph.coloringLLT_eraseNormal_descent
      (⟨G.normalEdges \ F, G.strictEdges⟩ : PairGraph n) a
      (hpath a (Finset.mem_insert_self _ _))]
    simp only [eraseNormal, Finset.sdiff_insert]

/-- Relabelling vertices by a permutation does not change the coloring polynomial. -/
theorem coloringLLT_relabel {m : ℕ} (π : Equiv.Perm (Fin n))
    (N S : Finset (Fin n × Fin n)) :
    (⟨N.map (Equiv.prodCongr π π).toEmbedding, S.map (Equiv.prodCongr π π).toEmbedding⟩ :
      PairGraph n).coloringLLT m = (⟨N, S⟩ : PairGraph n).coloringLLT m := by
  unfold coloringLLT
  let E : (Fin n → Fin m) ≃ (Fin n → Fin m) :=
    { toFun := fun c => c ∘ π.symm
      invFun := fun c => c ∘ π
      left_inv := fun c => by funext v; simp
      right_inv := fun c => by funext v; simp }
  rw [← Equiv.sum_comp E]
  apply Finset.sum_congr rfl
  intro c _
  change coloringWeight _ (c ∘ π.symm) = coloringWeight _ c
  unfold coloringWeight
  have hadm : admissible (⟨N.map (Equiv.prodCongr π π).toEmbedding,
      S.map (Equiv.prodCongr π π).toEmbedding⟩ : PairGraph n) (c ∘ π.symm) ↔
      admissible (⟨N, S⟩ : PairGraph n) c := by
    constructor
    · intro h e he
      have := h _ (Finset.mem_map_of_mem _ he)
      simpa using this
    · intro h e he
      obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
      have := h e' he'
      simpa using this
  have hasc : ascentCount (⟨N.map (Equiv.prodCongr π π).toEmbedding,
      S.map (Equiv.prodCongr π π).toEmbedding⟩ : PairGraph n) (c ∘ π.symm) =
      ascentCount (⟨N, S⟩ : PairGraph n) c := by
    unfold ascentCount
    simp only
    rw [Finset.filter_map, Finset.card_map]
    congr 1
    apply Finset.filter_congr
    intro e _
    simp
  have hmon : (∏ v, (MvPolynomial.X ((c ∘ π.symm) v) : XPoly m)) =
      ∏ v, MvPolynomial.X (c v) := by
    simpa [Function.comp_def] using
      (Equiv.prod_comp π.symm (fun v => (MvPolynomial.X (c v) : XPoly m)))
  simp only [hadm, hasc, hmon]

end PairGraph

namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- Restricted orientation sums over the subsets of a finite edge set. -/
noncomputable def orientSum (S : Finset (Edge D.area)) : EExpansion :=
  ∑ A ∈ S.powerset, MvPolynomial.C (Polynomial.X ^ A.card) * D.orientMono A

theorem shiftedOrientationExpansion_eq_orientSum :
    shiftedOrientationExpansion D = D.orientSum D.edgeData.normalEdges :=
  D.shiftedOrientationExpansion_eq_sum

theorem orientSum_forced (S : Finset (Edge D.area)) (hS : S ⊆ D.edgeData.normalEdges)
    (e : Edge D.area) (he : e ∈ S)
    (hpath : Relation.TransGen (D.edgeData.selected ∅) e.tail e.head) :
    D.orientSum S = MvPolynomial.C (Polynomial.X + 1) * D.orientSum (S.erase e) := by
  unfold orientSum
  conv_lhs => rw [← Finset.insert_erase he]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase e S)]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have hsub := Finset.mem_powerset.mp hA
  have hAe : e ∉ A := fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
  rw [D.orientMono_insert_of_strict_path e (hS he) hpath A
    ((hsub.trans (Finset.erase_subset _ _)).trans hS), Finset.card_insert_of_notMem hAe,
    pow_succ, MvPolynomial.C_mul, MvPolynomial.C_add, MvPolynomial.C_1]
  ring

theorem orientSum_descent (S : Finset (Edge D.area))
    (e : Edge D.area) (he : e ∈ S)
    (hpath : Relation.TransGen (D.edgeData.selected ∅) e.head e.tail) :
    D.orientSum S = D.orientSum (S.erase e) := by
  unfold orientSum
  conv_lhs => rw [← Finset.insert_erase he]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase e S)]
  simp only [D.orientMono_insert_of_reverse_strict_path e hpath,
    mul_zero, Finset.sum_const_zero, add_zero]

theorem orientSum_forced_set (S F : Finset (Edge D.area)) (hS : S ⊆ D.edgeData.normalEdges)
    (hF : F ⊆ S)
    (hpath : ∀ e ∈ F, Relation.TransGen (D.edgeData.selected ∅) e.tail e.head) :
    D.orientSum S = MvPolynomial.C (Polynomial.X + 1) ^ F.card * D.orientSum (S \ F) := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    rw [ih ((Finset.subset_insert _ _).trans hF)
      (fun e he => hpath e (Finset.mem_insert_of_mem he))]
    have hmem : a ∈ S \ F := Finset.mem_sdiff.mpr ⟨hF (Finset.mem_insert_self _ _), ha⟩
    rw [D.orientSum_forced (S \ F) ((Finset.sdiff_subset).trans hS) a hmem
      (hpath a (Finset.mem_insert_self _ _))]
    rw [Finset.card_insert_of_notMem ha, pow_succ, mul_assoc, Finset.sdiff_insert]

theorem orientSum_descent_set (S F : Finset (Edge D.area))
    (hF : F ⊆ S)
    (hpath : ∀ e ∈ F, Relation.TransGen (D.edgeData.selected ∅) e.head e.tail) :
    D.orientSum S = D.orientSum (S \ F) := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
    rw [ih ((Finset.subset_insert _ _).trans hF)
      (fun e he => hpath e (Finset.mem_insert_of_mem he))]
    have hmem : a ∈ S \ F := Finset.mem_sdiff.mpr ⟨hF (Finset.mem_insert_self _ _), ha⟩
    rw [D.orientSum_descent (S \ F) a hmem (hpath a (Finset.mem_insert_self _ _)),
      Finset.sdiff_insert]

/-- The edges whose endpoint pairs lie in a prescribed set. -/
noncomputable def edgesOfPairs (Ap : Finset (Fin n × Fin n)) : Finset (Edge D.area) :=
  Finset.univ.filter fun e => (e.tail, e.head) ∈ Ap

theorem mem_edgesOfPairs (Ap : Finset (Fin n × Fin n)) (e : Edge D.area) :
    e ∈ D.edgesOfPairs Ap ↔ (e.tail, e.head) ∈ Ap := by
  simp [edgesOfPairs]

theorem strictAt_iff_edge {y : ℤ} :
    D.strictAt y ↔ ∃ e ∈ D.strict, e.head = D.residue y := Iff.rfl

/-- A lifted selected step is a strict row or an edge lift with selected endpoint pair. -/
theorem liftStep_edgesOfPairs_iff (Ap : Finset (Fin n × Fin n)) (x y : ℤ) :
    D.liftStep (D.edgesOfPairs Ap) x y ↔
      (D.strictAt y ∧ x = D.boundary y) ∨
        (D.boundary y ≤ x ∧ x < y ∧ (D.residue x, D.residue y) ∈ Ap) := by
  constructor
  · rintro ⟨e, he, hx, hy⟩
    have hhead : D.residue y = e.head := by rw [hy]; exact D.residue_add_length e x hx
    rcases Finset.mem_union.mp he with hs | hA
    · left
      refine ⟨⟨e, hs, hhead.symm⟩, ?_⟩
      have hc := (D.strict_corner e hs).1
      rw [boundary, hhead, ← hc, hy]
      ring
    · right
      have hb := D.boundaryNaturalLift_of_edge (u := x) (v := y) hhead.symm (by rw [hy]; ring)
      refine ⟨hb.1, hb.2, ?_⟩
      rw [hx, hhead]
      exact (D.mem_edgesOfPairs Ap e).mp hA
  · rintro (⟨⟨e, he, hh⟩, hxb⟩ | ⟨hb, hxy, hp⟩)
    · refine ⟨e, Finset.mem_union_left _ he, ?_, ?_⟩
      · have hc := (D.strict_corner e he).1
        refine (D.residue_tail_of_length (u := x) hh ?_).symm
        rw [hxb, boundary, hc, hh]
        ring
      · have hc := (D.strict_corner e he).1
        rw [hxb, boundary, hc, hh]
        ring
    · have hl : D.boundaryNaturalLift x y := ⟨hb, hxy⟩
      refine ⟨D.edgeFromLift x y hl, Finset.mem_union_right _ ?_,
        (D.edgeFromLift_tail hl).symm, ?_⟩
      · rw [D.mem_edgesOfPairs, D.edgeFromLift_tail, D.edgeFromLift_head]
        exact hp
      · rw [D.edgeFromLift_length]
        ring

theorem residue_eq_of_window {a b lo hi : ℤ} (ha : lo ≤ a) (ha' : a ≤ hi) (hb : lo ≤ b)
    (hb' : b ≤ hi) (hw : hi - lo < n) (h : D.residue a = D.residue b) : a = b := by
  rcases le_total b a with hab | hab
  · exact D.eq_of_residue_eq_of_bounds h hab (by lia)
  · exact (D.eq_of_residue_eq_of_bounds h.symm hab (by lia)).symm

theorem residue_congr_diagram (D' : Diagram n) : D'.residue = D.residue := by
  funext z
  exact Fin.ext rfl

end Diagram

end VerticalStripLLT.Circular
