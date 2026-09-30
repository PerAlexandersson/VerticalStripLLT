import VerticalStripLLT.Components.DiagramProof.IncomingFlip
import VerticalStripLLT.Components.DiagramProof.RelationExchange
import VerticalStripLLT.Components.DiagramProof.FiniteCoverPaths

/-! The four actual flips that merge two children of one vertex. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

/-- A selected edge covers when every other outgoing target is a sink. -/
theorem relationCover_of_other_sinks {V : Type*} [LinearOrder V]
    {R : V → V → Prop} (hforward : ∀ ⦃u v⦄, R u v → u < v)
    {a t : V} (hat : R a t)
    (hother : ∀ w, R a w → w ≠ t → ∀ x, ¬ R w x) : RelationCover R a t := by
  refine ⟨hforward hat, Relation.ReflTransGen.single hat, ?_⟩
  intro w haw hwt hw
  rcases hw.1.cases_head with heq | ⟨q, haq, hqw⟩
  · exact haw.ne heq
  · have hqt : q ≠ t := by
      intro hqt
      subst q
      exact (not_le_of_gt hwt) (reachable_le hforward hqw)
    exact (hqt (reachable_eq_of_sink (hother q haq hqt)
      (hqw.trans hw.2)).symm).elim

private theorem childMerge_exchange (R : Fin n → Fin n → Prop)
    (z i j t : Fin n) (hzi : z ≠ i) (hzj : z ≠ j)
    (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t)
    (hrowz : ∀ v, R z v ↔ v = t)
    (hrowj : ∀ v, R j v ↔ v = t) (u v : Fin n) :
    exchangeRelation
      (exchangeRelation
        (exchangeRelation
          (exchangeRelation R i t z i) j t z j) z i i j) z j j t u v ↔
      exchangeRelation R i t i j u v := by
  simp only [exchangeRelation]
  grind

/-- Merge two children `i < j` of `t` by four actual flips, using the edge `zt`. -/
theorem exists_childMerge (hforward : Forward D) (θ : Orientation D)
    (z i j t : Fin n) (hzi : z < i) (hij : i < j) (hjt : j < t)
    (hrowz : ∀ v, D.edgeData.selected θ.val z v ↔ v = t)
    (hrowi : ∀ v, D.edgeData.selected θ.val i v ↔ v = t)
    (hrowj : ∀ v, D.edgeData.selected θ.val j v ↔ v = t) :
    ∃ η : Orientation D, Relation.ReflTransGen (Flip D) θ η ∧
      (∀ u v, D.edgeData.selected η.val u v ↔
        (u = i ∧ v = j) ∨
          (D.edgeData.selected θ.val u v ∧ ¬ (u = i ∧ v = t))) := by
  have hit : i < t := hij.trans hjt
  have hzj : z < j := hzi.trans hij
  have hjz : j ≠ z := hzj.ne.symm
  have hji : j ≠ i := hij.ne.symm
  have hztCover : Cover θ z t :=
    relationCover_of_first_outgoing
      (fun {_ _} h => θ.selected_lt_of_forward hforward h) ((hrowz t).mpr rfl) (by
        intro w _ hwt hw
        exact (hwt.ne ((hrowz w).mp hw)).elim)
  have hitCover : Cover θ i t :=
    relationCover_of_first_outgoing
      (fun {_ _} h => θ.selected_lt_of_forward hforward h) ((hrowi t).mpr rfl) (by
        intro w _ hwt hw
        exact (hwt.ne ((hrowi w).mp hw)).elim)
  have hjtCover : Cover θ j t :=
    relationCover_of_first_outgoing
      (fun {_ _} h => θ.selected_lt_of_forward hforward h) ((hrowj t).mpr rfl) (by
        intro w _ hwt hw
        exact (hwt.ne ((hrowj w).mp hw)).elim)
  obtain ⟨α, hθα, hαzt, hαzi, hα⟩ :=
    exists_incomingSwap_of_covers hforward θ z i t hitCover hztCover hzi
  have hrowjα : ∀ v, D.edgeData.selected α.val j v ↔ v = t := by
    intro v
    simpa only [hjz, hji, false_and, false_or, hrowj v, not_false_eq_true, and_true]
      using hα j v
  have hjtCoverα : Cover α j t :=
    relationCover_of_first_outgoing
      (fun {_ _} h => α.selected_lt_of_forward hforward h) ((hrowjα t).mpr rfl) (by
        intro w _ hwt hw
        exact (hwt.ne ((hrowjα w).mp hw)).elim)
  obtain ⟨β, hαβ, hβzt, hβzj, hβ⟩ :=
    exists_incomingSwap_of_covers hforward α z j t hjtCoverα hαzt hzj
  have hβzi : D.edgeData.selected β.val z i := by
    apply (hβ z i).mpr
    refine Or.inr ⟨rel_of_relationCover
      (fun {_ _} h => α.selected_lt_of_forward hforward h) hαzi, ?_⟩
    intro h
    exact (hzj.ne h.1).elim
  have hβziCover : Cover β z i :=
    relationCover_of_first_outgoing
      (fun {_ _} h => β.selected_lt_of_forward hforward h) hβzi (by
        intro w hzw hwi hw
        rcases (hβ z w).mp hw with ⟨_, hwj⟩ | ⟨hαzw, _⟩
        · rw [hwj] at hwi
          exact (not_lt_of_ge hij.le hwi).elim
        · rcases (hα z w).mp hαzw with ⟨_, hwi'⟩ | ⟨hθzw, _⟩
          · exact (hwi.ne hwi').elim
          · rw [(hrowz w).mp hθzw] at hwi
            exact (not_lt_of_ge hit.le hwi).elim)
  obtain ⟨γ, hβγ, hγzj, hγij, hγ⟩ :=
    exists_outgoingSwap_of_covers hforward β z i j hβziCover hβzj hij
  have hγzt : D.edgeData.selected γ.val z t := by
    apply (hγ z t).mpr
    refine Or.inr ⟨rel_of_relationCover
      (fun {_ _} h => β.selected_lt_of_forward hforward h) hβzt, ?_⟩
    intro h
    exact hit.ne.symm h.2
  have hjSinkγ : ∀ w, ¬ D.edgeData.selected γ.val j w := by
    intro w hw
    rcases (hγ j w).mp hw with ⟨hji', _⟩ | ⟨hβjw, _⟩
    · exact (hji hji').elim
    rcases (hβ j w).mp hβjw with ⟨hjz', _⟩ | ⟨hαjw, hjt'⟩
    · exact (hjz hjz').elim
    rcases (hα j w).mp hαjw with ⟨hjz', _⟩ | ⟨hθjw, _⟩
    · exact (hjz hjz').elim
    exact (hjt' ⟨rfl, (hrowj w).mp hθjw⟩).elim
  have hγztCover : Cover γ z t :=
    relationCover_of_other_sinks
      (fun {_ _} h => γ.selected_lt_of_forward hforward h) hγzt (by
        intro w hγzw hwt
        rcases (hγ z w).mp hγzw with ⟨hzi', _⟩ | ⟨hβzw, hnotzi⟩
        · exact (hzi.ne hzi').elim
        rcases (hβ z w).mp hβzw with ⟨_, hwj⟩ | ⟨hαzw, _⟩
        · subst w
          exact hjSinkγ
        rcases (hα z w).mp hαzw with ⟨_, hwi⟩ | ⟨hθzw, _⟩
        · exact (hnotzi ⟨rfl, hwi⟩).elim
        · exact (hwt ((hrowz w).mp hθzw)).elim)
  obtain ⟨η, hγη, _, _, hη⟩ :=
    exists_outgoingSwap_of_covers hforward γ z j t hγzj hγztCover hjt
  refine ⟨η, (((Relation.ReflTransGen.single hθα).tail hαβ).tail hβγ).tail hγη, ?_⟩
  have hβ' : ∀ u v, D.edgeData.selected β.val u v ↔
      exchangeRelation (exchangeRelation (D.edgeData.selected θ.val) i t z i) j t z j u v := by
    intro u v
    exact (hβ u v).trans (exchangeRelation_congr hα j t z j u v)
  have hγ' : ∀ u v, D.edgeData.selected γ.val u v ↔
      exchangeRelation
        (exchangeRelation (exchangeRelation (D.edgeData.selected θ.val) i t z i) j t z j)
        z i i j u v := by
    intro u v
    exact (hγ u v).trans (exchangeRelation_congr hβ' z i i j u v)
  have hη' : ∀ u v, D.edgeData.selected η.val u v ↔
      exchangeRelation
        (exchangeRelation
          (exchangeRelation (exchangeRelation (D.edgeData.selected θ.val) i t z i) j t z j)
          z i i j) z j j t u v := by
    intro u v
    exact (hη u v).trans (exchangeRelation_congr hγ' z j j t u v)
  intro u v
  exact (hη' u v).trans
    (childMerge_exchange _ z i j t hzi.ne hzj.ne hij.ne hit.ne hjt.ne
      hrowz hrowj u v)

end VerticalStripLLT.Circular.DiagramProof
