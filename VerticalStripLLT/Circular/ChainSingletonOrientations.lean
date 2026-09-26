import VerticalStripLLT.Circular.ChainSingletonAscentCount
import VerticalStripLLT.Circular.InsertionColorings
import VerticalStripLLT.Circular.ComparableExpansion
import VerticalStripLLT.Circular.HRVRoots
import VerticalStripLLT.Circular.HRVEvaluation
import VerticalStripLLT.Circular.StrictFibers

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace VerticalStripLLT.Circular.ChainSingletonData

variable {n k : ℕ} {D : Diagram n} (S : ChainSingletonData D k)

/-- The chain position of a vertex (the isolated vertex is sent to `0`). -/
noncomputable def chainIdx (u : Fin n) : Fin (k + 1) :=
  (S.vertices.symm u).elim id (fun _ => 0)

@[simp] theorem chainIdx_chain (i : Fin (k + 1)) : S.chainIdx (S.chain i) = i := by
  simp [chainIdx, chain]

theorem chain_chainIdx (u : Fin n) (hu : u ≠ S.isolated) : S.chain (S.chainIdx u) = u := by
  rcases S.vertex_cases u with ⟨i, rfl⟩ | rfl
  · rw [chainIdx_chain]
  · exact absurd rfl hu

theorem chain_ne_isolated (i : Fin (k + 1)) : S.chain i ≠ S.isolated :=
  fun h => S.isolated_ne_chain i h.symm

theorem chain_transGen_of_lt :
    ∀ (d : ℕ) (i j : Fin (k + 1)), j.val = i.val + d + 1 →
      Relation.TransGen (D.edgeData.selected ∅) (S.chain i) (S.chain j) := by
  intro d
  induction d with
  | zero =>
    intro i j hij
    have hk : i.val < k := by lia
    have h := S.selected_chain_succ ⟨i.val, hk⟩
    have e1 : (⟨i.val, hk⟩ : Fin k).castSucc = i := Fin.ext rfl
    have e2 : (⟨i.val, hk⟩ : Fin k).succ = j := Fin.ext (by simp; lia)
    rw [e1, e2] at h
    exact Relation.TransGen.single h
  | succ d ih =>
    intro i j hij
    have hk : j.val - 1 < k := by lia
    have h1 := ih i ⟨j.val - 1, by lia⟩ (by simp; lia)
    have h := S.selected_chain_succ ⟨j.val - 1, hk⟩
    have e1 : (⟨j.val - 1, hk⟩ : Fin k).castSucc = ⟨j.val - 1, by lia⟩ := Fin.ext rfl
    have e2 : (⟨j.val - 1, hk⟩ : Fin k).succ = j := Fin.ext (by simp; lia)
    rw [e1, e2] at h
    exact Relation.TransGen.tail h1 h

theorem chain_transGen {i j : Fin (k + 1)} (h : i < j) :
    Relation.TransGen (D.edgeData.selected ∅) (S.chain i) (S.chain j) :=
  S.chain_transGen_of_lt (j.val - i.val - 1) i j (by have := Fin.lt_def.mp h; lia)

theorem chain_reflTransGen {i j : Fin (k + 1)} (h : i ≤ j) :
    Relation.ReflTransGen (D.edgeData.selected ∅) (S.chain i) (S.chain j) := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact Relation.ReflTransGen.refl
  · exact (S.chain_transGen h).to_reflTransGen

theorem not_selected_empty_isolated (w : Fin n) :
    ¬ D.edgeData.selected ∅ S.isolated w := by
  intro h
  obtain ⟨i, hi, _⟩ := (S.strict_iff _ _).mp h
  exact S.isolated_ne_chain _ hi

theorem exists_strict_edge (i : Fin k) :
    ∃ e ∈ D.strict, e.tail = S.chain i.castSucc ∧ e.head = S.chain i.succ := by
  obtain ⟨e, he, ht, hh⟩ := S.selected_chain_succ i
  exact ⟨e, by simpa [Diagram.edgeData] using he, ht, hh⟩

theorem selected_of_empty {A : Finset (Edge D.area)} {u w : Fin n}
    (h : D.edgeData.selected ∅ u w) : D.edgeData.selected A u w := by
  obtain ⟨e, he, ht, hh⟩ := h
  exact ⟨e, Finset.union_subset_union_right (Finset.empty_subset _) he, ht, hh⟩

theorem selected_of_mem {A : Finset (Edge D.area)} {e : Edge D.area} (he : e ∈ A) :
    D.edgeData.selected A e.tail e.head :=
  ⟨e, Finset.mem_union_right _ he, rfl, rfl⟩

theorem selected_cases {A : Finset (Edge D.area)} {u w : Fin n}
    (h : D.edgeData.selected A u w) :
    D.edgeData.selected ∅ u w ∨ ∃ e ∈ A, e.tail = u ∧ e.head = w := by
  obtain ⟨e, he, ht, hh⟩ := h
  rcases Finset.mem_union.mp he with he | he
  · exact Or.inl ⟨e, by simpa using he, ht, hh⟩
  · exact Or.inr ⟨e, he, ht, hh⟩

theorem reflTransGen_of_empty {A : Finset (Edge D.area)} {u w : Fin n}
    (h : Relation.ReflTransGen (D.edgeData.selected ∅) u w) :
    Relation.ReflTransGen (D.edgeData.selected A) u w :=
  Relation.ReflTransGen.mono (fun _ _ h => selected_of_empty h) _ _ h

/-- Normal edges from the chain into the isolated vertex. -/
noncomputable def outEdges : Finset (Edge D.area) :=
  D.edgeData.normalEdges.filter (fun e => e.head = S.isolated)

/-- Normal edges from the isolated vertex into the chain. -/
noncomputable def inEdges : Finset (Edge D.area) :=
  D.edgeData.normalEdges.filter (fun e => e.tail = S.isolated)

theorem outEdges_tail {e : Edge D.area} (he : e ∈ S.outEdges) :
    e.tail ≠ S.isolated := by
  have hh := (Finset.mem_filter.mp he).2
  intro ht
  exact e.tail_ne_head (ht.trans hh.symm)

theorem inEdges_head {e : Edge D.area} (he : e ∈ S.inEdges) :
    e.head ≠ S.isolated := by
  have ht := (Finset.mem_filter.mp he).2
  intro hh
  exact e.tail_ne_head (ht.trans hh.symm)

theorem disjoint_out_in : Disjoint S.outEdges S.inEdges := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  exact S.outEdges_tail h1 (Finset.mem_filter.mp h2).2

/-- A selected incoming edge at or before a selected outgoing edge closes a cycle. -/
theorem not_admissible_of_le {A : Finset (Edge D.area)} {e f : Edge D.area}
    (he : e ∈ A) (heo : e ∈ S.outEdges) (hf : f ∈ A) (hfi : f ∈ S.inEdges)
    (hle : S.chainIdx f.head ≤ S.chainIdx e.tail) : ¬ D.edgeData.Admissible A := by
  intro hA
  apply hA S.isolated
  have h1 : D.edgeData.selected A S.isolated f.head := by
    have := selected_of_mem hf
    rwa [(Finset.mem_filter.mp hfi).2] at this
  have h2 : Relation.ReflTransGen (D.edgeData.selected A) f.head e.tail := by
    have := reflTransGen_of_empty (A := A) (S.chain_reflTransGen hle)
    rwa [S.chain_chainIdx _ (S.inEdges_head hfi), S.chain_chainIdx _ (S.outEdges_tail heo)]
      at this
  have h3 : D.edgeData.selected A e.tail S.isolated := by
    have := selected_of_mem he
    rwa [(Finset.mem_filter.mp heo).2] at this
  exact Relation.TransGen.tail (Relation.TransGen.head' h1 h2) h3

/-- If every selected outgoing edge precedes every selected incoming edge, there is no cycle. -/
theorem admissible_of_lt {A : Finset (Edge D.area)} (hA : A ⊆ S.outEdges ∪ S.inEdges)
    (hlt : ∀ e ∈ A ∩ S.outEdges, ∀ f ∈ A ∩ S.inEdges, S.chainIdx e.tail < S.chainIdx f.head) :
    D.edgeData.Admissible A := by
  let s : ℕ := (A ∩ S.outEdges).sup (fun e => (S.chainIdx e.tail).val + 1)
  let rank : Fin n → ℕ := fun u =>
    if u = S.isolated then 2 * s + 1 else 2 * (S.chainIdx u).val + 2
  have hstep : ∀ u w, D.edgeData.selected A u w → rank u < rank w := by
    intro u w h
    rcases selected_cases h with h | ⟨e, heA, rfl, rfl⟩
    · obtain ⟨i, rfl, rfl⟩ := (S.strict_iff _ _).mp h
      change rank (S.chain i.castSucc) < rank (S.chain i.succ)
      simp only [rank, ite_eq_right (S.chain_ne_isolated _), chainIdx_chain, Fin.val_castSucc,
        Fin.val_succ]
      lia
    · rcases Finset.mem_union.mp (hA heA) with heo | hei
      · have hh := (Finset.mem_filter.mp heo).2
        have hle : (S.chainIdx e.tail).val + 1 ≤ s :=
          Finset.le_sup (f := fun e => (S.chainIdx e.tail).val + 1)
            (Finset.mem_inter.mpr ⟨heA, heo⟩)
        simp only [rank, ite_eq_right (S.outEdges_tail heo), hh, ite_true]
        lia
      · have ht := (Finset.mem_filter.mp hei).2
        have hle : s ≤ (S.chainIdx e.head).val := by
          apply Finset.sup_le
          intro e' he'
          have := hlt e' he' e (Finset.mem_inter.mpr ⟨heA, hei⟩)
          have := Fin.lt_def.mp this
          lia
        simp only [rank, ite_eq_right (S.inEdges_head hei), ht, ite_true]
        lia
  intro v hv
  have : ∀ {u w}, Relation.TransGen (D.edgeData.selected A) u w → rank u < rank w := by
    intro u w h
    induction h with
    | single h => exact hstep _ _ h
    | tail _ h ih => exact ih.trans (hstep _ _ h)
  exact lt_irrefl _ (this hv)

theorem liftedHRV_eq_of_sink (θ : Orientation D) (z : ℤ)
    (hs : ∀ w, ¬ D.edgeData.selected θ.val (D.residue z) w) : θ.liftedHRV z = z := by
  have hreach_eq : ∀ w, Relation.ReflTransGen (D.liftStep θ.val) z w → w = z := by
    intro w hpath
    induction hpath with
    | refl => rfl
    | tail _ hstep ih =>
      have hselected := D.liftStep_selected hstep
      rw [ih] at hselected
      exact (hs _ hselected).elim
  exact hreach_eq _ (θ.liftedHRV_reachable z)

omit S in
theorem evalElementary_hrvMonomial_of_const (θ : Orientation D) (s0 : Fin n)
    (h : ∀ u, θ.hrv u = s0) (m : ℕ) :
    evalElementary m θ.hrvMonomial = MvPolynomial.esymm (Fin m) Q n := by
  rw [θ.evalElementary_hrvMonomial m, Finset.prod_eq_single s0]
  · congr 1
    rw [Finset.filter_true_of_mem (fun u _ => h u), Finset.card_univ, Fintype.card_fin]
  · intro r _ hr
    rw [Finset.filter_false_of_mem (fun u _ => by rw [h u]; exact Ne.symm hr),
      Finset.card_empty, MvPolynomial.esymm_zero]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

omit S in
theorem hrv_eq_of_unique_sink (θ : Orientation D) (s0 : Fin n)
    (h : ∀ w, (∀ w', ¬ D.edgeData.selected θ.val w w') → w = s0) (u : Fin n) :
    θ.hrv u = s0 :=
  h _ (fun w' hw => θ.hrv_is_sink u w' hw)

/-- The strict-only orientation. -/
noncomputable def emptyOrientation : Orientation D :=
  ⟨∅, Finset.empty_subset _, S.admissible_empty⟩

include S in
theorem strictOrderEnumerator_empty (m : ℕ) :
    D.edgeData.strictOrderEnumerator ∅ m =
      MvPolynomial.esymm (Fin m) Q 1 * MvPolynomial.esymm (Fin m) Q (k + 1) := by
  rw [← isolated_strictMono_sum (k + 1) m]
  unfold EdgeData.strictOrderEnumerator
  trans ∑ p : Fin m × (Fin (k + 1) → Fin m),
    (if ∀ e ∈ D.edgeData.strict ∪ ∅,
      ((S.coloringEquiv m).symm p) (D.edgeData.tail e) <
        ((S.coloringEquiv m).symm p) (D.edgeData.head e) then
      EdgeData.monomial ((S.coloringEquiv m).symm p) else 0)
  · refine Fintype.sum_equiv (S.coloringEquiv m) _ _ ?_
    intro c
    simp
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro c _
  have hiff : (∀ e ∈ D.edgeData.strict ∪ ∅,
      ((S.coloringEquiv m).symm (z, c)) (D.edgeData.tail e) <
        ((S.coloringEquiv m).symm (z, c)) (D.edgeData.head e)) ↔ StrictMono c := by
    rw [Finset.union_empty]
    have := S.admissibleColoring_iff ((S.coloringEquiv m).symm (z, c))
    simp only [coloringEquiv_symm_chain] at this
    exact this
  rw [if_congr hiff rfl rfl, S.monomial_coloringEquiv_symm]

/-- Outgoing edges before the last chain vertex do not change the strict HRV monomial. -/
theorem orientMono_of_early_out {A : Finset (Edge D.area)} (hA : A ⊆ S.outEdges)
    (hlast : ∀ e ∈ A, S.chainIdx e.tail ≠ Fin.last k) :
    D.orientMono A = S.emptyOrientation.hrvMonomial := by
  apply D.orientMono_noop S.emptyOrientation A
    (hA.trans (Finset.filter_subset _ _)) (Finset.empty_subset _)
  intro ε hε _
  have heo := hA hε
  have hne := S.outEdges_tail heo
  have hj := hlast ε hε
  have hjk : (S.chainIdx ε.tail).val < k := by
    have : (S.chainIdx ε.tail).val ≠ k := fun h => hj (Fin.ext (by simpa using h))
    have := (S.chainIdx ε.tail).isLt
    lia
  let i : Fin k := ⟨(S.chainIdx ε.tail).val, hjk⟩
  obtain ⟨e, he, het, _⟩ := S.exists_strict_edge i
  have hci : S.chain i.castSucc = ε.tail := by
    have : i.castSucc = S.chainIdx ε.tail := Fin.ext rfl
    rw [this, S.chain_chainIdx _ hne]
  rw [hci] at het
  let x : ℤ := (ε.tail.val : ℤ)
  have hx : D.residue x = ε.tail := Orientation.residue_intCast_eq ε.tail
  refine ⟨x, hx, ?_⟩
  have h1 : S.emptyOrientation.liftedHRV (x + ε.length.val) = x + ε.length.val := by
    apply liftedHRV_eq_of_sink
    rw [D.residue_add_length ε x hx, (Finset.mem_filter.mp heo).2]
    exact S.not_selected_empty_isolated
  have h2 : x + e.length.val ≤ S.emptyOrientation.liftedHRV x :=
    S.emptyOrientation.le_liftedHRV_of_reachable (Relation.ReflTransGen.single
      ⟨e, Finset.mem_union_left _ he, hx.trans het.symm, rfl⟩)
  have h3 : ε.length.val ≤ e.length.val := D.length_le_of_strict_same_tail he het.symm
  rw [h1]
  have h3' : (ε.length.val : ℤ) ≤ e.length.val := by exact_mod_cast h3
  linarith

theorem evalElementary_emptyOrientation (m : ℕ) :
    evalElementary m S.emptyOrientation.hrvMonomial =
      MvPolynomial.esymm (Fin m) Q 1 * MvPolynomial.esymm (Fin m) Q (k + 1) := by
  rw [← strictOrderEnumerator_eq_eval_hrvMonomial_of_empty S.emptyOrientation rfl m]
  exact S.strictOrderEnumerator_empty m

/-- The value of an external selection, indexed by outgoing and incoming chain positions. -/
noncomputable def selectionValue (k m : ℕ) (U V : Finset (Fin (k + 1))) : XPoly m :=
  if ∃ j ∈ U, ∃ h ∈ V, h ≤ j then 0 else
    if V.Nonempty ∨ Fin.last k ∈ U then MvPolynomial.esymm (Fin m) Q (k + 1 + 1)
    else MvPolynomial.esymm (Fin m) Q 1 * MvPolynomial.esymm (Fin m) Q (k + 1)

/-- The HRV classification of every external selection. -/
theorem eval_orientMono_external {A : Finset (Edge D.area)}
    (hA : A ⊆ S.outEdges ∪ S.inEdges) (m : ℕ) :
    evalElementary m (D.orientMono A) =
      selectionValue k m ((A ∩ S.outEdges).image (fun e => S.chainIdx e.tail))
        ((A ∩ S.inEdges).image (fun e => S.chainIdx e.head)) := by
  unfold selectionValue
  by_cases hbad : ∃ j ∈ (A ∩ S.outEdges).image (fun e => S.chainIdx e.tail),
      ∃ h ∈ (A ∩ S.inEdges).image (fun e => S.chainIdx e.head), h ≤ j
  · rw [ite_eq_left hbad]
    obtain ⟨j, hj, h, hh, hle⟩ := hbad
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hh
    rw [Finset.mem_inter] at he hf
    rw [D.orientMono_of_not_adm (S.not_admissible_of_le he.1 he.2 hf.1 hf.2 hle), map_zero]
  rw [ite_eq_right hbad]
  push Not at hbad
  have hlt : ∀ e ∈ A ∩ S.outEdges, ∀ f ∈ A ∩ S.inEdges,
      S.chainIdx e.tail < S.chainIdx f.head := fun e he f hf =>
    hbad _ (Finset.mem_image_of_mem _ he) _ (Finset.mem_image_of_mem _ hf)
  have hadm := S.admissible_of_lt hA hlt
  have hAN : A ⊆ D.edgeData.normalEdges :=
    hA.trans (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  by_cases hone : ((A ∩ S.inEdges).image (fun e => S.chainIdx e.head)).Nonempty ∨
      Fin.last k ∈ (A ∩ S.outEdges).image (fun e => S.chainIdx e.tail)
  · rw [ite_eq_left hone]
    let θ : Orientation D := ⟨A, hAN, hadm⟩
    have hθ : D.orientMono A = θ.hrvMonomial := D.orientMono_orientation θ
    let s0 : Fin n := if ((A ∩ S.inEdges).image (fun e => S.chainIdx e.head)).Nonempty then
      S.chain (Fin.last k) else S.isolated
    have hsink : ∀ w, (∀ w', ¬ D.edgeData.selected θ.val w w') → w = s0 := by
      intro w hw
      rcases S.vertex_cases w with ⟨i, rfl⟩ | rfl
      · have hi : i = Fin.last k := by
          by_contra hi
          have hik : i.val < k := by
            have : i.val ≠ k := fun h => hi (Fin.ext (by simpa using h))
            have := i.isLt
            lia
          have h := S.selected_chain_succ ⟨i.val, hik⟩
          have e1 : (⟨i.val, hik⟩ : Fin k).castSucc = i := Fin.ext rfl
          rw [e1] at h
          exact hw _ (selected_of_empty h)
        subst hi
        by_cases hV : ((A ∩ S.inEdges).image (fun e => S.chainIdx e.head)).Nonempty
        · simp only [s0, ite_eq_left hV]
        · have hl := hone.resolve_left hV
          obtain ⟨e, he, hel⟩ := Finset.mem_image.mp hl
          rw [Finset.mem_inter] at he
          exfalso
          apply hw S.isolated
          have := selected_of_mem he.1
          rwa [(Finset.mem_filter.mp he.2).2, ← S.chain_chainIdx _ (S.outEdges_tail he.2), hel]
            at this
      · by_cases hV : ((A ∩ S.inEdges).image (fun e => S.chainIdx e.head)).Nonempty
        · exfalso
          obtain ⟨h, hh⟩ := hV
          obtain ⟨f, hf, _⟩ := Finset.mem_image.mp hh
          rw [Finset.mem_inter] at hf
          apply hw f.head
          have := selected_of_mem hf.1
          rwa [(Finset.mem_filter.mp hf.2).2] at this
        · simp only [s0, ite_eq_right hV]
    rw [hθ, evalElementary_hrvMonomial_of_const θ s0 (hrv_eq_of_unique_sink θ s0 hsink) m]
    congr 1
    exact S.cardinality
  · rw [ite_eq_right hone]
    push Not at hone
    have hAo : A ⊆ S.outEdges := by
      intro e he
      rcases Finset.mem_union.mp (hA he) with h | h
      · exact h
      · exfalso
        exact Finset.not_nonempty_iff_eq_empty.mpr hone.1
          ⟨_, Finset.mem_image_of_mem _ (Finset.mem_inter.mpr ⟨he, h⟩)⟩
    have hlast : ∀ e ∈ A, S.chainIdx e.tail ≠ Fin.last k := by
      intro e he hl
      exact hone.2 (hl ▸ Finset.mem_image_of_mem _ (Finset.mem_inter.mpr ⟨he, hAo he⟩))
    rw [S.orientMono_of_early_out hAo hlast, S.evalElementary_emptyOrientation m]

end VerticalStripLLT.Circular.ChainSingletonData
