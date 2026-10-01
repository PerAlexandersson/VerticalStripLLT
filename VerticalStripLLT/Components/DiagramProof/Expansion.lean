import VerticalStripLLT.Components.DiagramProof.PrefixAttachment
import VerticalStripLLT.Components.DiagramProof.DisjointUnion

/-!
# The ordinary component expansion by diagrams

Every whole flip component of a forward (ordinary) diagram satisfies

    K(C) = E(C),

that is, its strict-coloring enumerator equals the evaluation of its HRV
elementary expansion, for every finite alphabet.

The proof is strong induction on the vertex count, the natural area and the area
moment, ordered lexicographically:

* disjoint natural components factor over smaller vertex sets;
* a component without a connected common-cover witness has a certificate by
  missing-corner deletion, weak-block reordering or alternating corner deletion;
* a witness component is first saturated; a saturated path has a single state
  whose two values agree; otherwise the first nontrivial prefix carries a
  right-marked NN or DN certificate, and the right attachment glues it to an
  unmarked certificate by smaller whole components.

The proof uses the diagram paths and identities only. It does not import the
earlier word-functional component theorem.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

variable {k : ℕ} {D : Diagram (k + 1)}

/-! ### The path base -/

/-- A diagram all of whose natural edges are adjacent has no actual flips. -/
theorem not_flip_of_adjacent_only (hD : Forward D)
    (hpath : ∀ u v, naturalRel D u v → v.val = u.val + 1) (θ η : Orientation D) :
    ¬ Flip D θ η := by
  have hno : ∀ θ η : Orientation D, ¬ DirectedFlip D θ η := by
    intro θ η hf
    obtain ⟨a, b, c, hbc, hab, hac, -⟩ := (directedFlip_iff hD θ η).mp hf
    have hn := hpath a c (naturalRel_of_selected (selected_of_cover hD hac))
    have h1 : a.val < b.val := hab.1
    have h2 : b.val < c.val := hbc
    lia
  rintro (h | h)
  · exact hno θ η h
  · exact hno η θ h

theorem flipComponent_eq_singleton_of_adjacent_only (hD : Forward D)
    (hpath : ∀ u v, naturalRel D u v → v.val = u.val + 1) (θ : Orientation D) :
    flipComponent D θ = {θ} := by
  ext η
  rw [mem_flipComponent_iff, Finset.mem_singleton]
  constructor
  · intro hp
    rcases hp.cases_tail with rfl | ⟨ζ, -, hζη⟩
    · rfl
    · exact (not_flip_of_adjacent_only hD hpath ζ η hζη).elim
  · rintro rfl
    exact Relation.ReflTransGen.refl

/-- The transitive closure of the adjacent chain is the order. -/
theorem transGen_adjacent_iff (R : Fin (k + 1) → Fin (k + 1) → Prop)
    (hR : ∀ u v, R u v ↔ v.val = u.val + 1) (u v : Fin (k + 1)) :
    Relation.TransGen R u v ↔ u < v := by
  constructor
  · intro h
    induction h with
    | single h' => rename_i b; rw [Fin.lt_def, (hR _ _).mp h']; lia
    | tail _ h' ih => rename_i b c; exact ih.trans (by rw [Fin.lt_def, (hR _ _).mp h']; lia)
  · intro huv
    have key : ∀ d (w : Fin (k + 1)), w.val = u.val + d + 1 → Relation.TransGen R u w := by
      intro d
      induction d with
      | zero =>
        intro w hw
        exact Relation.TransGen.single ((hR u w).mpr (by lia))
      | succ d ih =>
        intro w hw
        have hw' : u.val + d + 1 < k + 1 := by have := w.isLt; lia
        exact (ih ⟨u.val + d + 1, hw'⟩ rfl).tail ((hR _ _).mpr (by simp; lia))
    have huv' : u.val < v.val := huv
    exact key (v.val - u.val - 1) v (by lia)

/-- **The path base.** A component of a connected path diagram with a witness has
equal values. -/
theorem component_eq_of_path (hD : Forward D) (hadj : AdjacentEdges D)
    (hpath : ∀ u v, naturalRel D u v → v.val = u.val + 1) (θ : Orientation D)
    (hθ : HasCommonWitness θ) (m : ℕ) :
    componentStrictEnumerator D θ m = evalElementary m (componentHRV D θ) := by
  have hcomp := flipComponent_eq_singleton_of_adjacent_only hD hpath θ
  obtain ⟨η, hη, -, hcov⟩ := hθ
  rw [hcomp, Finset.mem_singleton] at hη
  subst hη
  -- Every natural pair is a selected corner.
  have hsel : ∀ u v, D.edgeData.selected η.val u v ↔ v.val = u.val + 1 := by
    intro u v
    constructor
    · exact fun h => hpath u v (naturalRel_of_selected h)
    · intro huv
      obtain ⟨e, rfl, rfl⟩ := hadj u v huv
      have heC : IsCorner e := by
        rw [isCorner_iff_maximalPair hD]
        refine ⟨⟨e, rfl, rfl⟩, fun x y hxy hx hy => ?_⟩
        have h1 := hpath x y hxy
        have h2 : x.val ≤ e.tail.val := hx
        have h3 : e.head.val ≤ y.val := hy
        exact ⟨Fin.ext (by lia), Fin.ext (by lia)⟩
      exact selected_of_cover hD (hcov e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heC⟩))
  -- Every vertex reaches the greatest vertex.
  have hhrv : ∀ u, η.hrv u = Fin.last k := by
    intro u
    apply le_antisymm (Fin.le_last _)
    apply η.reachable_le_hrv_of_forward hD
    rcases eq_or_lt_of_le (Fin.le_last u) with h | h
    · rw [h]
    · exact ((transGen_adjacent_iff _ hsel u _).mpr h).to_reflTransGen
  have hclosure : Relation.TransGen (D.edgeData.selected η.val) =
      Relation.TransGen (fibreRelation η.hrv) := by
    funext u v
    apply propext
    rw [transGen_adjacent_iff _ hsel]
    constructor
    · intro huv
      exact Relation.TransGen.single ⟨huv, by rw [hhrv, hhrv]⟩
    · intro h
      induction h with
      | single h' => exact h'.1
      | tail _ h' ih => exact ih.trans h'.1
  unfold componentStrictEnumerator componentHRV
  rw [hcomp, Finset.sum_singleton, Finset.sum_singleton, ← sum_markedE η 0 m,
    ← relationValue_selected, ← sum_markedRelationValue _ (0 : Fin (k + 1))]
  exact Finset.sum_congr rfl fun β _ =>
    markedRelationValue_eq_of_transGen_eq _ _ hclosure 0 m β

/-! ### Natural disconnection -/

theorem exists_cut_of_not_adjacent (hD : Forward D) (hadj : ¬ AdjacentEdges D) :
    ∃ p' q', k = p' + 1 + q' ∧
      ∀ e : Edge D.area, e.tail.val < p' + 1 → e.head.val < p' + 1 := by
  unfold AdjacentEdges at hadj
  push Not at hadj
  obtain ⟨u, v, huv, hno⟩ := hadj
  refine ⟨u.val, k - v.val, by have := v.isLt; lia, ?_⟩
  intro e he
  by_contra hhead
  apply hno
  apply naturalRel_sub hD ⟨e, rfl, rfl⟩
  · show e.tail.val ≤ u.val
    lia
  · rw [Fin.lt_def, huv]
    lia
  · show v.val ≤ e.head.val
    lia

/-! ### Maximal corners along paths -/

/-- A maximal natural pair is never an exchanged short, so its selection is constant
along actual paths. -/
theorem selected_maximal_iff_of_flip (hD : Forward D) {θ η : Orientation D}
    (hf : Flip D θ η) {s t : Fin (k + 1)} (hst : MaximalPair (naturalRel D) s t) :
    D.edgeData.selected θ.val s t ↔ D.edgeData.selected η.val s t := by
  have key : ∀ {θ η : Orientation D}, DirectedFlip D θ η →
      (D.edgeData.selected θ.val s t ↔ D.edgeData.selected η.val s t) := by
    intro θ η hf
    obtain ⟨a, b, c, hbc, hab, hac, hη⟩ := (directedFlip_iff hD θ η).mp hf
    have hnat := naturalRel_of_selected (selected_of_cover hD hac)
    have hne1 : ¬ (s = b ∧ t = c) := by
      rintro ⟨rfl, rfl⟩
      exact hab.1.ne (hst.2 a t hnat hab.1.le le_rfl).1
    have hne2 : ¬ (s = a ∧ t = b) := by
      rintro ⟨rfl, rfl⟩
      exact hbc.ne (hst.2 s c hnat le_rfl hbc.le).2.symm
    rw [hη]
    unfold swapRel
    simp only [hne1, hne2, false_or, not_false_eq_true, and_true]
  rcases hf with hf | hf
  · exact key hf
  · exact (key hf).symm

theorem selected_maximal_iff_of_reachable (hD : Forward D) {θ η : Orientation D}
    (hp : Relation.ReflTransGen (Flip D) θ η) {s t : Fin (k + 1)}
    (hst : MaximalPair (naturalRel D) s t) :
    D.edgeData.selected θ.val s t ↔ D.edgeData.selected η.val s t := by
  induction hp with
  | refl => exact Iff.rfl
  | tail _ hstep ih => exact ih.trans (selected_maximal_iff_of_flip hD hstep hst)

/-! ### The induction -/

/-- The diagram-route theorem, by strong induction on `(n, area, moment)`. -/
theorem component_eq_by_diagrams_aux :
    ∀ (n A M : ℕ) (D : Diagram n), Forward D → naturalArea D = A → areaMoment D = M →
      ∀ (θ : Orientation D) (m : ℕ),
        componentStrictEnumerator D θ m = evalElementary m (componentHRV D θ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ihn =>
  intro A
  induction A using Nat.strong_induction_on with
  | h A ihA =>
  intro M
  induction M using Nat.strong_induction_on with
  | h M ihM =>
  intro D hD hA hM θ m
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := D.area.positive; lia⟩
  -- A certificate by smaller whole components suffices.
  have hcert : ∀ (E : Diagram (k + 1)) (hE : Forward E) (η : Orientation E),
      naturalArea E = A → areaMoment E = M → (∃ c : Cert k, UCertifies ⟨E, hE, η⟩ c) →
      ∀ m, componentStrictEnumerator E η m = evalElementary m (componentHRV E η) := by
    rintro E hE η hEA hEM ⟨c, hc⟩ m
    rw [(hc.1 m).1, (hc.1 m).2]
    unfold Cert.KU Cert.EU
    simp only [Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy' : componentStrictEnumerator y.D y.θ m = evalElementary m (componentHRV y.D y.θ) := by
      rcases hc.2 y hy with hlt | ⟨heq, hlt⟩
      · exact ihA _ (hlt.trans_eq hEA) _ y.D y.forward rfl rfl y.θ m
      · exact ihM _ (hlt.trans_eq hEM) y.D y.forward (heq.trans hEA) rfl y.θ m
    rw [hy']
  by_cases hadj : AdjacentEdges D
  · by_cases hw : HasCommonWitness θ
    · by_cases hnp : ∃ u v : Fin (k + 1), naturalRel D u v ∧ u.val + 2 ≤ v.val
      · -- Saturate: the same whole component, with every maximal corner strict.
        have hall : ∀ s t, MaximalPair (naturalRel D) s t → D.edgeData.selected θ.val s t := by
          obtain ⟨η, hη, -, hcov⟩ := hw
          intro s t hst
          obtain ⟨e, rfl, rfl⟩ := hst.1
          have heC := (isCorner_iff_maximalPair hD e).mpr hst
          have hsel := selected_of_cover hD (hcov e (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, heC⟩))
          exact (selected_maximal_iff_of_reachable hD (mem_flipComponent_iff.mp hη) hst).mpr
            hsel
        obtain ⟨θs, hcs⟩ := exists_saturate hD θ hall
        have hDs := saturate_forward hD
        have hnat : ∀ a b, naturalRel D a b ↔ naturalRel (saturate hD) a b :=
          fun a b => (saturate_naturalRel hD a b).symm
        obtain ⟨hAs, hMs⟩ := measure_eq_of_naturalRel_iff hnat
        have hws := hasCommonWitness_of_corresponds hD hDs hnat hcs hw
        have hadjs : AdjacentEdges (saturate hD) := fun u v huv => (hnat u v).mp (hadj u v huv)
        have hsats : ∀ s t, MaximalPair (naturalRel (saturate hD)) s t →
            strictRel (saturate hD) s t := by
          intro s t hst
          rw [saturate_strictRel]
          exact ⟨(hnat s t).mpr hst.1, fun x y hxy => hst.2 x y ((hnat x y).mp hxy)⟩
        have hnps : ∃ u v : Fin (k + 1), naturalRel (saturate hD) u v ∧ u.val + 2 ≤ v.val := by
          obtain ⟨u, v, huv, hgap⟩ := hnp
          exact ⟨u, v, (hnat u v).mp huv, hgap⟩
        have hs := hcert (saturate hD) hDs θs (hAs ▸ hA) (hMs ▸ hM)
          (uCertifies_of_witness hDs hadjs hsats hnps θs hws) m
        have hK : componentStrictEnumerator D θ m = componentStrictEnumerator _ θs m := by
          rw [← sum_componentMarkedK θ (Fin.last k) m, ← sum_componentMarkedK θs (Fin.last k) m]
          exact Finset.sum_congr rfl fun β _ => (hcs.componentMarkedK_eq hD hDs rfl m β).symm
        have hE : evalElementary m (componentHRV D θ) =
            evalElementary m (componentHRV _ θs) := by
          rw [← sum_componentMarkedE θ (Fin.last k) m, ← sum_componentMarkedE θs (Fin.last k) m]
          exact Finset.sum_congr rfl fun β _ => (hcs.componentMarkedE_eq hD hDs rfl m β).symm
        rw [hK, hE, hs]
      · -- A path.
        push Not at hnp
        refine component_eq_of_path hD hadj (fun u v huv => ?_) θ hw m
        have h1 : u.val < v.val := naturalRel_forward hD huv
        have h2 := hnp u v huv
        lia
    · exact hcert D hD θ hA hM ((certifies_of_not_hasCommonWitness hD hadj.connected θ hw).imp
        fun _ h => h.uCertifies) m
  · -- Disjoint natural components.
    obtain ⟨p', q', rfl, hcut⟩ := exists_cut_of_not_adjacent hD hadj
    have h := isDisjointUnion_induced (p' := p') (q' := q') hD hcut
    rw [← h.glue_restrict θ, h.componentStrictEnumerator_glue,
      h.evalElementary_componentHRV_glue,
      ihn _ (by lia) _ _ _ h.forwardL rfl rfl, ihn _ (by lia) _ _ _ h.forwardR rfl rfl]

end

end VerticalStripLLT.Circular.DiagramProof
