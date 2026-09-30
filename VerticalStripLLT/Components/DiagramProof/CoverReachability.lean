import VerticalStripLLT.Components.DiagramProof.ForkNormalization
import VerticalStripLLT.Components.DiagramProof.FiniteCoverPaths
import VerticalStripLLT.Components.DiagramProof.WeakBlocks

/-! Consequences of having at most one outgoing cover at each vertex. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

/-- With unique outgoing covers, every selected path has a common greatest reachable vertex. -/
theorem hrv_eq_of_reachable_of_rightUnique_covers (hforward : Forward D)
    {θ : Orientation D} (hunique : Relator.RightUnique (Cover θ))
    {u v : Fin n} (hp : Relation.ReflTransGen (D.edgeData.selected θ.val) u v) :
    θ.hrv u = θ.hrv v :=
  terminal_eq_of_reachable_of_reachable_sink
    (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) hunique θ.hrv
    θ.hrv_reachable θ.hrv_is_sink hp

/-- Unique outgoing covers make the HRV map constant on each selected weak component. -/
theorem hrv_eq_of_weakReach_of_rightUnique_covers (hforward : Forward D)
    {θ : Orientation D} (hunique : Relator.RightUnique (Cover θ))
    {u v : Fin n} (hp : WeakReach θ u v) : θ.hrv u = θ.hrv v := by
  induction hp with
  | rel a b hs =>
    exact hrv_eq_of_reachable_of_rightUnique_covers hforward hunique
      (Relation.ReflTransGen.single hs)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- In a connected state with unique outgoing covers, every vertex reaches the greatest one. -/
theorem reachable_top_of_connected_of_rightUnique_covers (hforward : Forward D)
    {θ : Orientation D} (hunique : Relator.RightUnique (Cover θ))
    (hconnected : SelectedConnected θ) (t : Fin n) (ht : ∀ v, v ≤ t) (v : Fin n) :
    Relation.ReflTransGen (D.edgeData.selected θ.val) v t := by
  have hterminal : θ.hrv t = t := le_antisymm (ht _)
    (reachable_le (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) (θ.hrv_reachable t))
  have hv : θ.hrv v = t :=
    (hrv_eq_of_weakReach_of_rightUnique_covers hforward hunique (hconnected v t)).trans hterminal
  exact hv ▸ θ.hrv_reachable v

/-- A child of a sink has no selected outgoing edge other than its edge to that sink. -/
theorem selected_target_eq_of_cover_to_sink (hforward : Forward D)
    {θ : Orientation D} (hunique : Relator.RightUnique (Cover θ))
    {u t : Fin n} (hcover : Cover θ u t)
    (hsink : ∀ v, ¬ D.edgeData.selected θ.val t v)
    {v : Fin n} (hselected : D.edgeData.selected θ.val u v) : v = t := by
  have hp := relationCover_path_of_rel
    (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) hselected
  rcases hp.cases_head with heq | ⟨w, huw, hwv⟩
  · exact ((θ.selected_lt_of_forward hforward hselected).ne heq).elim
  · have hwt : w = t := hunique huw hcover
    subst w
    exact reachable_eq_of_sink hsink (reachable_of_relationCover_path
      (fun {_ _} hs => θ.selected_lt_of_forward hforward hs) hwv)

/-- In particular, a cover to the greatest vertex is its source's sole outgoing selected edge. -/
theorem selected_iff_eq_top_of_cover (hforward : Forward D)
    {θ : Orientation D} (hunique : Relator.RightUnique (Cover θ))
    {u t : Fin n} (hcover : Cover θ u t) (ht : ∀ v, v ≤ t) (v : Fin n) :
    D.edgeData.selected θ.val u v ↔ v = t := by
  constructor
  · exact selected_target_eq_of_cover_to_sink hforward hunique hcover
      (fun w hs => not_lt_of_ge (ht w) (θ.selected_lt_of_forward hforward hs))
  · intro hv
    subst v
    exact selected_of_cover hforward hcover

end VerticalStripLLT.Circular.DiagramProof
