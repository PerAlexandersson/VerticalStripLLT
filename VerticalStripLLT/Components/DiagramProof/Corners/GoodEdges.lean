import VerticalStripLLT.Components.DiagramProof.Corners.CornerChains

/-! Terminal-increasing normal edges give simultaneous corner covers. -/

namespace VerticalStripLLT.Circular.DiagramProof

/-- In a forward relation with unique successors, every edge is a cover. -/
theorem relationCover_of_rightUnique {V : Type*} [LinearOrder V] {R : V → V → Prop}
    (hforward : ∀ ⦃u v⦄, R u v → u < v) (hunique : Relator.RightUnique R)
    {u v : V} (huv : R u v) : RelationCover R u v := by
  refine ⟨hforward huv, Relation.ReflTransGen.single huv, ?_⟩
  intro w huw hwv hw
  rcases hw.1.cases_head with heq | ⟨z, huz, hzw⟩
  · exact huw.ne heq
  · have hz : z = v := hunique huz huv
    subst z
    exact (not_le_of_gt hwv) (reachable_le hforward hzw)

namespace CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- Allowed anchor edges: retained corners or edges increasing the chain terminal. -/
def GoodEdge (e : Edge D.area) : Prop :=
  e ∈ F.edges ∨ F.terminal hforward e.tail < F.terminal hforward e.head

/-- An anchor selects all retained corners and only good extra edges. -/
def Anchor (θ : Orientation D) : Prop :=
  F.edges ⊆ fullSelection θ ∧ ∀ e ∈ fullSelection θ, F.GoodEdge hforward e

/-- The fixed finite set of all possible anchor edges. -/
noncomputable def goodEdges : Finset (Edge D.area) := by
  classical
  exact Finset.univ.filter (F.GoodEdge hforward)

@[simp] theorem mem_goodEdges (e : Edge D.area) :
    e ∈ F.goodEdges hforward ↔ F.GoodEdge hforward e := by
  classical
  simp only [goodEdges, Finset.mem_filter, Finset.mem_univ, true_and]

theorem anchor_iff_subsets (θ : Orientation D) :
    F.Anchor hforward θ ↔ F.edges ⊆ fullSelection θ ∧
      fullSelection θ ⊆ F.goodEdges hforward := by
  constructor
  · rintro ⟨hc, hg⟩
    exact ⟨hc, fun e he => (F.mem_goodEdges hforward e).mpr (hg e he)⟩
  · rintro ⟨hc, hg⟩
    exact ⟨hc, fun e he => (F.mem_goodEdges hforward e).mp (hg he)⟩

/-- Every subset of the good-edge set containing the corners is an actual anchor. -/
theorem anchor_ofFullSelection (A : Finset (Edge D.area)) (hC : F.edges ⊆ A)
    (hA : A ⊆ F.goodEdges hforward) :
    F.Anchor hforward (ofFullSelection hforward A (F.contains_strict.trans hC)) := by
  rw [F.anchor_iff_subsets hforward, fullSelection_ofFullSelection]
  exact ⟨hC, hA⟩

/-- A common-cover state, the starting condition for corner-chain preparation. -/
def CommonCover (θ : Orientation D) : Prop := ∀ e ∈ F.edges, Cover θ e.tail e.head

theorem terminal_le_of_good {e : Edge D.area} (he : F.GoodEdge hforward e) :
    F.terminal hforward e.tail ≤ F.terminal hforward e.head := by
  rcases he with he | he
  · exact ((F.terminal_eq_iff_mem hforward e).mpr he).le
  · exact he.le

theorem selected_terminal_le {θ : Orientation D}
    (hgood : ∀ e ∈ fullSelection θ, F.GoodEdge hforward e)
    {u v : Fin n} (h : D.edgeData.selected θ.val u v) :
    F.terminal hforward u ≤ F.terminal hforward v := by
  obtain ⟨e, he, rfl, rfl⟩ := h
  exact F.terminal_le_of_good hforward (hgood e he)

theorem reachable_terminal_le {θ : Orientation D}
    (hgood : ∀ e ∈ fullSelection θ, F.GoodEdge hforward e)
    {u v : Fin n} (h : Relation.ReflTransGen (D.edgeData.selected θ.val) u v) :
    F.terminal hforward u ≤ F.terminal hforward v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact ih.trans (F.selected_terminal_le hforward hgood hs)

/-- An equal-terminal path in good edges uses only corner edges. -/
theorem reachable_step_of_terminal_eq {θ : Orientation D}
    (hgood : ∀ e ∈ fullSelection θ, F.GoodEdge hforward e)
    {u v : Fin n} (h : Relation.ReflTransGen (D.edgeData.selected θ.val) u v)
    (heq : F.terminal hforward u = F.terminal hforward v) :
    Relation.ReflTransGen F.step u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail v w hp hs ih =>
    have huv := F.reachable_terminal_le hforward hgood hp
    have hvw := F.selected_terminal_le hforward hgood hs
    have huvEq := le_antisymm huv (hvw.trans_eq heq.symm)
    have hvwEq := huvEq.symm.trans heq
    obtain ⟨e, _, het, heh⟩ := hs
    have he : e ∈ F.edges := F.mem_of_terminal_eq hforward e (by
      change e.tail = v at het
      change e.head = w at heh
      simpa only [het, heh] using hvwEq)
    exact (ih huvEq).tail ((F.step_iff v w).mpr ⟨e, he, het, heh⟩)

/-- Every retained corner covers in every subset of the fixed good-edge diagram. -/
theorem commonCover_of_anchor {θ : Orientation D} (hθ : F.Anchor hforward θ) :
    F.CommonCover θ := by
  intro e he
  have hs : F.step e.tail e.head := (F.step_iff _ _).mpr ⟨e, he, rfl, rfl⟩
  have hc := relationCover_of_rightUnique (fun {_ _} h => F.step_forward hforward h)
    F.step_rightUnique hs
  have heq := F.terminal_eq_of_step hforward hs
  refine ⟨hforward e, Relation.ReflTransGen.single
    ((mem_fullSelection_iff_selected θ e).mp (hθ.1 he)), ?_⟩
  intro w htw hwh hw
  have htw' := F.reachable_terminal_le hforward hθ.2 hw.1
  have hwh' := F.reachable_terminal_le hforward hθ.2 hw.2
  have hteq := le_antisymm htw' (hwh'.trans_eq heq.symm)
  exact hc.2.2 w htw hwh
    ⟨F.reachable_step_of_terminal_eq hforward hθ.2 hw.1 hteq,
      F.reachable_step_of_terminal_eq hforward hθ.2 hw.2 (hteq.symm.trans heq)⟩

include hforward in
/-- Common-cover states already select every retained corner. -/
theorem subset_fullSelection_of_commonCover {θ : Orientation D} (hθ : F.CommonCover θ) :
    F.edges ⊆ fullSelection θ := by
  intro e he
  exact (mem_fullSelection_iff_selected θ e).mpr (selected_of_cover hforward (hθ e he))

end CornerFamily

end VerticalStripLLT.Circular.DiagramProof
