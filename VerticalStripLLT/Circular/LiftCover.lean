import VerticalStripLLT.Circular.LiftStep

/-! Natural lifted edges and the full integer cover relation. -/

namespace VerticalStripLLT.Circular

namespace Diagram

variable {n : ℕ} (D : Diagram n)

/-- An integer lift of one specified edge instance. -/
def naturalLift (e : Edge D.area) (x y : ℤ) : Prop :=
  D.residue x = e.tail ∧ y = x + (e.length.val : ℤ)

/-- A cover in the full integer lift relation. -/
def liftCover (A : Finset (Edge D.area)) (x y : ℤ) : Prop :=
  x < y ∧ Relation.ReflTransGen (D.liftStep A) x y ∧
    ∀ z, x < z → z < y →
      ¬ (Relation.ReflTransGen (D.liftStep A) x z ∧
        Relation.ReflTransGen (D.liftStep A) z y)

theorem reachability_nonneg {A : Finset (Edge D.area)} {x y : ℤ}
    (h : Relation.ReflTransGen (D.liftStep A) x y) : x ≤ y := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    have hpos := (D.liftStep_bounds hstep).1
    lia

theorem liftCover_liftStep {A : Finset (Edge D.area)} {x y : ℤ}
    (h : D.liftCover A x y) : D.liftStep A x y := by
  rcases h with ⟨hxy, hreach, hcover⟩
  rcases Relation.ReflTransGen.cases_head hreach with rfl | ⟨z, hxz, hzy⟩
  · lia
  · by_cases hzy_eq : z = y
    · simpa [hzy_eq] using hxz
    · have hxz_pos := (D.liftStep_bounds hxz).1
      have hxz_lt : x < z := by lia
      have hzy_le := D.reachability_nonneg hzy
      have hzy_lt : z < y := by lia
      exact False.elim (hcover z hxz_lt hzy_lt ⟨
        Relation.ReflTransGen.single hxz, hzy⟩)

theorem naturalLift_injective {e f : Edge D.area} {x y : ℤ}
    (he : D.naturalLift e x y) (hf : D.naturalLift f x y) : e = f := by
  have hlen : e.length.val = f.length.val := by
    have heq := he.2
    have hfq := hf.2
    lia
  have htail : e.tail = f.tail := he.1.symm.trans hf.1
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    have he' := e.tail_add_length_mod
    have hf' := f.tail_add_length_mod
    rw [hlen, htail] at he'
    exact he'.symm.trans hf'
  · apply Fin.ext
    exact hlen

theorem liftStep_of_naturalLift_of_mem {A : Finset (Edge D.area)}
    {e : Edge D.area} {x y : ℤ} (he : e ∈ D.strict ∪ A)
    (hnat : D.naturalLift e x y) : D.liftStep A x y := by
  exact ⟨e, he, hnat.1, hnat.2⟩

theorem mem_selected_of_naturalLift_of_liftCover
    {A : Finset (Edge D.area)} {e : Edge D.area} {x y : ℤ}
    (hnat : D.naturalLift e x y) (hcov : D.liftCover A x y) :
    e ∈ D.strict ∪ A := by
  rcases D.liftCover_liftStep hcov with ⟨f, hf, hres, hxy⟩
  have hnatf : D.naturalLift f x y := ⟨hres, hxy⟩
  have hef : e = f := D.naturalLift_injective hnat hnatf
  simpa [hef] using hf

end Diagram
end VerticalStripLLT.Circular
