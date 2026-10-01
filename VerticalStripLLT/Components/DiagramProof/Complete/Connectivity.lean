import VerticalStripLLT.Components.DiagramProof.Complete.ChordConnectivityStep
import VerticalStripLLT.Components.DiagramProof.Complete.Small
import VerticalStripLLT.Components.DiagramProof.Complete.FiveVertexBase

/-! Complete-diagram connectivity at a fixed total selected-edge count. -/

namespace VerticalStripLLT.Circular.DiagramProof

/-- Connected states covering the extreme corner in a complete diagram lie in
one actual flip component at each fixed total selected-edge count. -/
theorem complete_reachable (n : ℕ) (θ η : Orientation (completeDiagram n))
    (hθ : SelectedConnected θ) (hcθ : Cover θ 0 (Fin.last n))
    (hη : SelectedConnected η) (hcη : Cover η 0 (Fin.last n))
    (htotal : totalSelected θ = totalSelected η) :
    Relation.ReflTransGen (Flip (completeDiagram n)) θ η := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n ≤ 3
    · exact complete_reachable_of_le_three hsmall θ η hθ hcθ hη hcη htotal
    by_cases hfour : n = 4
    · subst n
      exact complete_reachable_five θ η hθ hcθ hη hcη htotal
    exact complete_reachable_of_smaller (by lia) ih θ η hθ hcθ hη hcη htotal

/-- The same connectivity holds with the extreme corner strict throughout the path. -/
theorem complete_reachable_marked (n : ℕ) (hn : 0 < n)
    (θ η : Orientation (completeCornerDiagram n hn))
    (hθ : SelectedConnected θ) (hcθ : Cover θ 0 (Fin.last n))
    (hη : SelectedConnected η) (hcη : Cover η 0 (Fin.last n))
    (htotal : totalSelected θ = totalSelected η) :
    Relation.ReflTransGen (Flip (completeCornerDiagram n hn)) θ η := by
  let θ₀ : Orientation (completeDiagram n) := θ.toUndecorated
  let η₀ : Orientation (completeDiagram n) := η.toUndecorated
  have hrelθ : (completeDiagram n).edgeData.selected θ₀.val =
      (completeCornerDiagram n hn).edgeData.selected θ.val := θ.toUndecorated_selected
  have hrelη : (completeDiagram n).edgeData.selected η₀.val =
      (completeCornerDiagram n hn).edgeData.selected η.val := η.toUndecorated_selected
  have hconnectedθ : SelectedConnected θ₀ := by
    simpa only [SelectedConnected, WeakReach, hrelθ] using hθ
  have hconnectedη : SelectedConnected η₀ := by
    simpa only [SelectedConnected, WeakReach, hrelη] using hη
  have hcoverθ : Cover θ₀ 0 (Fin.last n) := by simpa only [Cover, hrelθ] using hcθ
  have hcoverη : Cover η₀ 0 (Fin.last n) := by simpa only [Cover, hrelη] using hcη
  have hcount : totalSelected θ₀ = totalSelected η₀ :=
    (totalSelected_toUndecorated θ).trans (htotal.trans (totalSelected_toUndecorated η).symm)
  exact reachable_toUndecorated_iff.mp
    (complete_reachable n θ₀ η₀ hconnectedθ hcoverθ hconnectedη hcoverη hcount)

end VerticalStripLLT.Circular.DiagramProof
