import VerticalStripLLT.Circular.EdgeDeletion
import VerticalStripLLT.Circular.EdgeBounds
import VerticalStripLLT.Circular.Coloring

/-! Corner strictification and deletion for circular diagrams. -/

namespace VerticalStripLLT.Circular

namespace CircularArea

variable {n : ℕ}

/-- Lower the area of one column by one. -/
def lowerAt (A : CircularArea n) (h : Fin n) (hpos : 0 < A.area h)
    (hc : A.area (A.next h) ≤ A.area h) : CircularArea n where
  positive := A.positive
  area := Function.update A.area h (A.area h - 1)
  bound := by
    intro i
    by_cases hi : i = h
    · subst hi; simp only [Function.update_self]; have := A.bound i; lia
    · simp only [ne_eq, hi, not_false_eq_true, Function.update_of_ne]; exact A.bound i
  cyclic := by
    intro i
    have hcyc := A.cyclic i
    have hcyc' : A.area (A.next i) ≤ A.area i + 1 := hcyc
    change Function.update A.area h (A.area h - 1) (A.next i) ≤
      Function.update A.area h (A.area h - 1) i + 1
    by_cases hi : i = h
    · subst hi
      by_cases hn : A.next i = i
      · rw [hn]; simp
      · rw [Function.update_of_ne hn, Function.update_self]; lia
    · rw [Function.update_of_ne hi]
      by_cases hn : A.next i = h
      · rw [hn, Function.update_self]; rw [hn] at hcyc'; lia
      · rw [Function.update_of_ne hn]; exact hcyc'

theorem lowerAt_area_le (A : CircularArea n) (h : Fin n) (hpos : 0 < A.area h)
    (hc : A.area (A.next h) ≤ A.area h) (i : Fin n) :
    (A.lowerAt h hpos hc).area i ≤ A.area i := by
  change Function.update A.area h (A.area h - 1) i ≤ A.area i
  by_cases hi : i = h
  · subst hi; simp
  · rw [Function.update_of_ne hi]

theorem lowerAt_area_of_ne (A : CircularArea n) (h : Fin n) (hpos : 0 < A.area h)
    (hc : A.area (A.next h) ≤ A.area h) {i : Fin n} (hi : i ≠ h) :
    (A.lowerAt h hpos hc).area i = A.area i := by
  change Function.update A.area h (A.area h - 1) i = A.area i
  rw [Function.update_of_ne hi]

theorem lowerAt_area_self (A : CircularArea n) (h : Fin n) (hpos : 0 < A.area h)
    (hc : A.area (A.next h) ≤ A.area h) :
    (A.lowerAt h hpos hc).area h = A.area h - 1 := by
  change Function.update A.area h (A.area h - 1) h = _
  simp

end CircularArea

namespace Diagram

variable {n : ℕ}

noncomputable section

theorem corner_area_pos {A : CircularArea n} {e : Edge A} (he : IsCorner e) :
    0 < A.area e.head := by
  have := e.length_pos; have := he.1; lia

/-- Make a corner strict. -/
def strictify (D : Diagram n) (e : Edge D.area) (he : IsCorner e) : Diagram n where
  area := D.area
  strict := insert e D.strict
  strict_corner := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact he
    · exact D.strict_corner f hf

/-- The area sequence obtained by removing a corner edge. -/
def cornerArea (D : Diagram n) (e : Edge D.area) (he : IsCorner e) : CircularArea n :=
  D.area.lowerAt e.head (corner_area_pos he) he.2

/-- Include an edge of the lowered area into the original area. -/
def cornerIncl (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (f : Edge (D.cornerArea e he)) : Edge D.area :=
  ⟨f.1, f.2.1, le_trans f.2.2 (CircularArea.lowerAt_area_le _ _ _ _ _)⟩

theorem cornerIncl_ne (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (f : Edge (D.cornerArea e he)) : D.cornerIncl e he f ≠ e := by
  intro hfe
  have h1 : f.1.1 = e.1.1 := congrArg (fun g : Edge D.area => g.1.1) hfe
  have h2 : f.1.2 = e.1.2 := congrArg (fun g : Edge D.area => g.1.2) hfe
  have hle := f.2.2
  have hself := CircularArea.lowerAt_area_self D.area e.head (corner_area_pos he) he.2
  have hlen : e.length.val = D.area.area e.head := he.1
  have hpos := corner_area_pos he
  change f.1.2.val ≤ (D.cornerArea e he).area f.1.1 at hle
  rw [h1, h2] at hle
  change e.length.val ≤ (D.area.lowerAt e.head _ _).area e.head at hle
  rw [hself] at hle
  lia

theorem cornerIncl_injective (D : Diagram n) (e : Edge D.area) (he : IsCorner e) :
    Function.Injective (D.cornerIncl e he) := by
  intro f g hfg
  apply Subtype.ext
  exact congrArg (fun g : Edge D.area => g.1) hfg

/-- Every other edge survives the removal of a corner. -/
def cornerRestrict (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (f : Edge D.area) (hf : f ≠ e) : Edge (D.cornerArea e he) :=
  ⟨f.1, f.2.1, by
    by_cases hh : f.1.1 = e.head
    · have hlen : e.length.val = D.area.area e.head := he.1
      have hle : f.1.2.val ≤ D.area.area f.1.1 := f.2.2
      have hne : f.1.2.val ≠ e.length.val := by
        intro h
        apply hf
        apply Subtype.ext
        exact Prod.ext hh (Fin.ext h)
      change f.1.2.val ≤ (D.area.lowerAt e.head _ _).area f.1.1
      rw [hh, CircularArea.lowerAt_area_self]
      rw [hh] at hle
      lia
    · change f.1.2.val ≤ (D.area.lowerAt e.head _ _).area f.1.1
      rw [CircularArea.lowerAt_area_of_ne _ _ _ _ hh]
      exact f.2.2⟩

/-- Edges of the lowered area are the edges other than the removed corner. -/
def cornerEquiv (D : Diagram n) (e : Edge D.area) (he : IsCorner e) :
    Edge (D.cornerArea e he) ≃ {f : Edge D.area // f ≠ e} where
  toFun f := ⟨D.cornerIncl e he f, D.cornerIncl_ne e he f⟩
  invFun f := D.cornerRestrict e he f.1 f.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Remove a corner edge. -/
def deleteCorner (D : Diagram n) (e : Edge D.area) (he : IsCorner e) : Diagram n where
  area := D.cornerArea e he
  strict := Finset.univ.filter fun f => D.cornerIncl e he f ∈ D.strict
  strict_corner := by
    intro f hf
    have hs : D.cornerIncl e he f ∈ D.strict := (Finset.mem_filter.mp hf).2
    have hc := D.strict_corner _ hs
    have hne : f.1.1 ≠ e.head := by
      intro hh
      have hlen1 : f.1.2.val = D.area.area f.1.1 := hc.1
      have hle : f.1.2.val ≤ (D.cornerArea e he).area f.1.1 := f.2.2
      change f.1.2.val ≤ (D.area.lowerAt e.head _ _).area f.1.1 at hle
      rw [hh, CircularArea.lowerAt_area_self] at hle
      rw [hh] at hlen1
      have := corner_area_pos he
      lia
    constructor
    · change f.1.2.val = (D.area.lowerAt e.head _ _).area f.1.1
      rw [CircularArea.lowerAt_area_of_ne _ _ _ _ hne]
      exact hc.1
    · change (D.area.lowerAt e.head _ _).area (D.area.next f.1.1) ≤
        (D.area.lowerAt e.head _ _).area f.1.1
      rw [CircularArea.lowerAt_area_of_ne _ _ _ _ hne]
      exact le_trans (CircularArea.lowerAt_area_le _ _ _ _ _) hc.2

theorem strictify_edgeData (D : Diagram n) (e : Edge D.area) (he : IsCorner e) :
    (D.strictify e he).edgeData = D.edgeData.withStrict e := rfl

/-- Shifted LLT deletion–contraction at a non-strict corner. -/
theorem xQShift_coloringLLT_corner (D : Diagram n) (e : Edge D.area) (he : IsCorner e)
    (hns : e ∉ D.strict) (m : ℕ) :
    xQShift m (D.coloringLLT m) =
      MvPolynomial.C Polynomial.X * xQShift m ((D.strictify e he).coloringLLT m) +
        xQShift m ((D.deleteCorner e he).coloringLLT m) := by
  unfold coloringLLT
  rw [D.edgeData.xQShift_coloringLLT_deletion e hns m, strictify_edgeData]
  congr 2
  symm
  apply EdgeData.coloringLLT_congr _ _ (D.cornerEquiv e he)
  · intro f; rfl
  · intro f; rfl
  · intro f
    change f ∈ Finset.univ.filter (fun f => D.cornerIncl e he f ∈ D.strict) ↔ _
    simp [EdgeData.delete, cornerEquiv]
    rfl

end

end Diagram

end VerticalStripLLT.Circular
