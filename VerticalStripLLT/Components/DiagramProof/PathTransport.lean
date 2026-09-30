import VerticalStripLLT.Components.DiagramProof.Basic
import VerticalStripLLT.Components.ForwardHRVBasic
import VerticalStripLLT.Components.ForwardFlipNormalization

/-!
# Ordinary covers and actual flip witnesses

The finite cover predicate below is equivalent to the existing full integer-lift
cover predicate. It is an interface for diagram paths, not a replacement flip model.
-/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {D : Diagram n}

/-- A cover in the selected forward relation on the actual finite vertex set. -/
def Cover (θ : Orientation D) (u v : Fin n) : Prop :=
  u < v ∧ Relation.ReflTransGen (D.edgeData.selected θ.val) u v ∧
    ∀ w, u < w → w < v →
      ¬ (Relation.ReflTransGen (D.edgeData.selected θ.val) u w ∧
        Relation.ReflTransGen (D.edgeData.selected θ.val) w v)

theorem liftReach_iff_reachable (hforward : Forward D) (θ : Orientation D)
    (u v : Fin n) :
    Relation.ReflTransGen (D.liftStep θ.val) (u.val : ℤ) (v.val : ℤ) ↔
      Relation.ReflTransGen (D.edgeData.selected θ.val) u v := by
  constructor
  · intro h
    have hp := h.lift D.residue (fun _ _ hs => D.liftStep_selected hs)
    change Relation.ReflTransGen (D.edgeData.selected θ.val)
      (D.residue (u.val : ℤ)) (D.residue (v.val : ℤ)) at hp
    simpa only [Orientation.residue_intCast_eq] using hp
  · exact θ.reachable_lift_of_forward hforward

theorem liftCover_iff_cover (hforward : Forward D) (θ : Orientation D)
    (u v : Fin n) :
    D.liftCover θ.val (u.val : ℤ) (v.val : ℤ) ↔ Cover θ u v := by
  constructor
  · rintro ⟨huv, hreach, hcover⟩
    refine ⟨by exact_mod_cast huv, (liftReach_iff_reachable hforward θ u v).mp hreach, ?_⟩
    intro w huw hwv hw
    exact hcover (w.val : ℤ) (by exact_mod_cast huw) (by exact_mod_cast hwv)
      ⟨(liftReach_iff_reachable hforward θ u w).mpr hw.1,
        (liftReach_iff_reachable hforward θ w v).mpr hw.2⟩
  · rintro ⟨huv, hreach, hcover⟩
    refine ⟨by exact_mod_cast huv, (liftReach_iff_reachable hforward θ u v).mpr hreach, ?_⟩
    intro z huz hzv hz
    obtain ⟨w, rfl⟩ := θ.liftReach_canonical_of_forward hforward hz.1
    exact hcover w (by exact_mod_cast huz) (by exact_mod_cast hzv)
      ⟨(liftReach_iff_reachable hforward θ u w).mp hz.1,
        (liftReach_iff_reachable hforward θ w v).mp hz.2⟩

theorem selected_of_cover (hforward : Forward D) {θ : Orientation D}
    {u v : Fin n} (h : Cover θ u v) : D.edgeData.selected θ.val u v := by
  have hs := D.liftStep_selected
    (D.liftCover_liftStep ((liftCover_iff_cover hforward θ u v).mpr h))
  simpa only [Orientation.residue_intCast_eq] using hs

theorem cover_of_selected_adjacent {θ : Orientation D} {u v : Fin n}
    (h : D.edgeData.selected θ.val u v) (hadj : v.val = u.val + 1) : Cover θ u v := by
  refine ⟨by change u.val < v.val; lia, Relation.ReflTransGen.single h, ?_⟩
  intro w huw hwv _
  have huw' : u.val < w.val := huw
  have hwv' : w.val < v.val := hwv
  lia

/-- Finite cover data constructs an existing actual directed flip witness. -/
def directedFlipOfCovers (hforward : Forward D) {θ η : Orientation D}
    {a b c : Fin n} (hab : a < b) (hbc : b < c)
    (eab ebc : Edge D.area)
    (habtail : eab.tail = a) (habhead : eab.head = b)
    (hbctail : ebc.tail = b) (hbchead : ebc.head = c)
    (habnormal : eab ∈ D.edgeData.normalEdges)
    (hbcnormal : ebc ∈ D.edgeData.normalEdges)
    (hsab : Cover θ a b) (hsac : Cover θ a c) (hsnbc : ¬ Cover θ b c)
    (htac : Cover η a c) (htbc : Cover η b c) (htnab : ¬ Cover η a b)
    (hagree : ∀ e, e ≠ eab → e ≠ ebc → (e ∈ θ.val ↔ e ∈ η.val)) :
    DirectedFlipWitness D θ η where
  a := a.val
  b := b.val
  c := c.val
  cyclicWindow := by
    have hcn : c.val < n := c.isLt
    have hab' : a.val < b.val := hab
    have hbc' : b.val < c.val := hbc
    exact ⟨by exact_mod_cast hab', by exact_mod_cast hbc', by lia⟩
  eab := eab
  ebc := ebc
  eab_normal := habnormal
  ebc_normal := hbcnormal
  ab_lift := by
    simpa only [habtail, habhead] using D.naturalLift_of_tail_lt_head eab (hforward eab)
  bc_lift := by
    simpa only [hbctail, hbchead] using D.naturalLift_of_tail_lt_head ebc (hforward ebc)
  source_ab := (liftCover_iff_cover hforward θ a b).mpr hsab
  source_ac := (liftCover_iff_cover hforward θ a c).mpr hsac
  source_not_bc := fun h => hsnbc ((liftCover_iff_cover hforward θ b c).mp h)
  target_ac := (liftCover_iff_cover hforward η a c).mpr htac
  target_bc := (liftCover_iff_cover hforward η b c).mpr htbc
  target_not_ab := fun h => htnab ((liftCover_iff_cover hforward η a b).mp h)
  agree_elsewhere := hagree

end VerticalStripLLT.Circular.DiagramProof
