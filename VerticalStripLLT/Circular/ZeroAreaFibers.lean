import VerticalStripLLT.Circular.HRVRoots
import VerticalStripLLT.Circular.ZeroArea

/-! Functional selected relations and HRV fibers in the zero-normal case. -/

namespace VerticalStripLLT.Circular

namespace Orientation

variable {n : ℕ} {D : Diagram n}

theorem val_eq_empty_of_no_normal (hN : D.edgeData.normalEdges = ∅)
    (θ : Orientation D) : θ.val = ∅ := by
  apply Finset.subset_empty.mp
  rw [← hN]
  exact θ.property.1

theorem selected_rightUnique_of_no_normal (hN : D.edgeData.normalEdges = ∅)
    (θ : Orientation D) : Relator.RightUnique (D.edgeData.selected θ.val) := by
  intro u v w huv huw
  rcases huv with ⟨e, he, htail, hhead⟩
  rcases huw with ⟨f, hf, htail', hhead'⟩
  have hef : e = f := D.edge_eq_of_tail_eq_of_no_normal hN (htail.trans htail'.symm)
  calc
    v = e.head := hhead.symm
    _ = f.head := congrArg Edge.head hef
    _ = w := hhead'

theorem selected_leftUnique_of_no_normal (hN : D.edgeData.normalEdges = ∅)
    (θ : Orientation D) : Relator.LeftUnique (D.edgeData.selected θ.val) := by
  intro u v w huv hwv
  rcases huv with ⟨e, he, htail, hhead⟩
  rcases hwv with ⟨f, hf, htail', hhead'⟩
  have hef : e = f := D.edge_eq_of_head_eq_of_no_normal hN (hhead.trans hhead'.symm)
  calc
    u = e.tail := htail.symm
    _ = f.tail := congrArg Edge.tail hef
    _ = v := htail'

theorem hrv_reachable (θ : Orientation D) (u : Fin n) :
    Relation.ReflTransGen (D.edgeData.selected θ.val) u (θ.hrv u) := by
  have h := θ.liftedHRV_reachable (u.val : ℤ)
  have hp := Relation.ReflTransGen.lift D.residue
    (fun _ _ hstep => D.liftStep_selected hstep) _ _ h
  simpa [Function.onFun, hrv, residue_intCast_eq] using hp

private theorem rtc_eq_of_sink {α : Type*} {r : α → α → Prop} {u v : α}
    (hsink : ∀ w, ¬ r u w) (h : Relation.ReflTransGen r u v) : v = u := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    rw [ih] at hstep
    exact (hsink _ hstep).elim

theorem hrv_eq_of_selected_of_no_normal (hN : D.edgeData.normalEdges = ∅)
    (θ : Orientation D) {u v : Fin n}
    (h : D.edgeData.selected θ.val u v) : θ.hrv u = θ.hrv v := by
  have huv := Relation.ReflTransGen.single h
  have hpath : Relation.ReflTransGen (D.edgeData.selected θ.val) u (θ.hrv v) :=
    huv.trans (θ.hrv_reachable v)
  have hleft := θ.hrv_reachable u
  have htotal := Relation.ReflTransGen.total_of_right_unique
    (selected_rightUnique_of_no_normal hN θ) hleft hpath
  have hsinku : ∀ w, ¬ D.edgeData.selected θ.val (θ.hrv u) w :=
    fun w hw => θ.hrv_is_sink u w hw
  have hsinkv : ∀ w, ¬ D.edgeData.selected θ.val (θ.hrv v) w :=
    fun w hw => θ.hrv_is_sink v w hw
  rcases htotal with huv' | hvu'
  · exact (rtc_eq_of_sink hsinku huv').symm
  · exact (rtc_eq_of_sink hsinkv hvu')

theorem hrv_eq_of_reachable_of_no_normal (hN : D.edgeData.normalEdges = ∅)
    (θ : Orientation D) {u v : Fin n}
    (h : Relation.ReflTransGen (D.edgeData.selected θ.val) u v) :
    θ.hrv u = θ.hrv v := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    exact ih.trans (θ.hrv_eq_of_selected_of_no_normal hN hstep)

theorem same_hrv_comparable_of_no_normal (hN : D.edgeData.normalEdges = ∅)
    (θ : Orientation D) {u v : Fin n} (h : θ.hrv u = θ.hrv v) :
    Relation.ReflTransGen (D.edgeData.selected θ.val) u v ∨
      Relation.ReflTransGen (D.edgeData.selected θ.val) v u := by
  let r := D.edgeData.selected θ.val
  have hleft : Relator.LeftUnique r := selected_leftUnique_of_no_normal hN θ
  have hu : Relation.ReflTransGen (Function.swap r) (θ.hrv u) u :=
    Relation.reflTransGen_swap.mpr (θ.hrv_reachable u)
  have hv : Relation.ReflTransGen (Function.swap r) (θ.hrv u) v := by
    rw [h]
    exact Relation.reflTransGen_swap.mpr (θ.hrv_reachable v)
  have htotal := Relation.ReflTransGen.total_of_right_unique hleft.flip
    hu hv
  rcases htotal with huv | hvu
  · exact Or.inr (Relation.reflTransGen_swap.mp huv)
  · exact Or.inl (Relation.reflTransGen_swap.mp hvu)

end Orientation
end VerticalStripLLT.Circular
