import VerticalStripLLT.Circular.ZeroAreaFibers
import VerticalStripLLT.Circular.NeutralContacts

/-! HRV fibers for an orientation whose selected normal set is empty. -/

namespace VerticalStripLLT.Circular

namespace Orientation

variable {n : ℕ} {D : Diagram n} (θ : Orientation D)

private theorem rtc_eq_of_sink {α : Type*} {r : α → α → Prop} {u v : α}
    (hsink : ∀ w, ¬ r u w) (h : Relation.ReflTransGen r u v) : v = u := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    rw [ih] at hstep
    exact (hsink _ hstep).elim

theorem selected_rightUnique_of_empty (hθ : θ.val = ∅) :
    Relator.RightUnique (D.edgeData.selected θ.val) := by
  simpa [hθ] using D.strict_selected_rightUnique

theorem selected_leftUnique_of_empty (hθ : θ.val = ∅) :
    Relator.LeftUnique (D.edgeData.selected θ.val) := by
  simpa [hθ] using D.strict_selected_leftUnique

theorem hrv_eq_of_selected_of_empty (hθ : θ.val = ∅) {u v : Fin n}
    (h : D.edgeData.selected θ.val u v) : θ.hrv u = θ.hrv v := by
  have huv := Relation.ReflTransGen.single h
  have hpath : Relation.ReflTransGen (D.edgeData.selected θ.val) u (θ.hrv v) :=
    huv.trans (θ.hrv_reachable v)
  have hleft := θ.hrv_reachable u
  have htotal := Relation.ReflTransGen.total_of_right_unique
    (θ.selected_rightUnique_of_empty hθ) hleft hpath
  have hsinku : ∀ w, ¬ D.edgeData.selected θ.val (θ.hrv u) w :=
    fun w hw => θ.hrv_is_sink u w hw
  have hsinkv : ∀ w, ¬ D.edgeData.selected θ.val (θ.hrv v) w :=
    fun w hw => θ.hrv_is_sink v w hw
  rcases htotal with huv' | hvu'
  · exact (rtc_eq_of_sink hsinku huv').symm
  · exact rtc_eq_of_sink hsinkv hvu'

theorem hrv_eq_of_reachable_of_empty (hθ : θ.val = ∅) {u v : Fin n}
    (h : Relation.ReflTransGen (D.edgeData.selected θ.val) u v) :
    θ.hrv u = θ.hrv v := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    exact ih.trans (θ.hrv_eq_of_selected_of_empty hθ hstep)

theorem same_hrv_comparable_of_empty (hθ : θ.val = ∅) {u v : Fin n}
    (h : θ.hrv u = θ.hrv v) :
    Relation.ReflTransGen (D.edgeData.selected θ.val) u v ∨
      Relation.ReflTransGen (D.edgeData.selected θ.val) v u := by
  let r := D.edgeData.selected θ.val
  have hleft : Relator.LeftUnique r := θ.selected_leftUnique_of_empty hθ
  have hu : Relation.ReflTransGen (Function.swap r) (θ.hrv u) u :=
    Relation.reflTransGen_swap.mpr (θ.hrv_reachable u)
  have hv : Relation.ReflTransGen (Function.swap r) (θ.hrv u) v := by
    rw [h]
    exact Relation.reflTransGen_swap.mpr (θ.hrv_reachable v)
  have htotal := Relation.ReflTransGen.total_of_right_unique hleft.flip hu hv
  rcases htotal with huv | hvu
  · exact Or.inr (Relation.reflTransGen_swap.mp huv)
  · exact Or.inl (Relation.reflTransGen_swap.mp hvu)

end Orientation
end VerticalStripLLT.Circular
