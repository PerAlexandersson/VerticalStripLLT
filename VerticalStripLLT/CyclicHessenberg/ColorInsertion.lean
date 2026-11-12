import VerticalStripLLT.CyclicHessenberg.ColorDegree

/-! Finite insertion of the largest vertex through an ordered alphabet of color weights. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {V R : Type*} [CommRing R]

/-- Ordered product of the decreasing class factors for all colors. -/
noncomputable def colorClassProduct (l : List V) : List R → WordSum R V
  | [] => 1
  | t :: Y => descendingClass t l * colorClassProduct l Y

/-- Insert the largest vertex by conjugating the insertion for the remaining colors. -/
noncomputable def colorInsertion (l : List V) (r : V) : List R → WordSum R V
  | [] => 0
  | t :: Y => t • wordTerm [r] +
      descendingClass t l * colorInsertion l r Y * inverseClass t l

/-- Every insertion term contains its root, so an additional copy annihilates it. -/
theorem colorInsertion_repeated_root (f : List V → R)
    (hrep : ∀ l, ¬ l.Nodup → f l = 0) (l : List V) (r : V)
    (Y : List R) (A : WordSum R V) :
    ContextEq f (wordTerm [r] * A * colorInsertion l r Y) 0 := by
  induction Y generalizing A with
  | nil => simp only [colorInsertion, mul_zero]; exact ContextEq.refl _
  | cons t Y ih =>
    have h₁ := (repeated_sandwich f hrep r A).smul t
    have h₂ := (ih (A * descendingClass t l)).mul_right (inverseClass t l)
    simpa only [colorInsertion, mul_add, mul_smul_comm, zero_mul, smul_zero,
      add_zero, mul_assoc] using h₁.add h₂

/-- Factor the product of color classes using the actual insertion recursion. -/
theorem colorClassProduct_insert_root (f : List V → R)
    (hrep : ∀ l, ¬ l.Nodup → f l = 0) (l : List V) (r : V) (Y : List R) :
    ContextEq f (colorClassProduct (l ++ [r]) Y)
      ((1 + colorInsertion l r Y) * colorClassProduct l Y) := by
  induction Y with
  | nil => simp only [colorClassProduct, colorInsertion, add_zero, mul_one]; exact ContextEq.refl _
  | cons t Y ih =>
    let T : WordSum R V := t • wordTerm [r]
    let D : WordSum R V := descendingClass t l
    let I : WordSum R V := inverseClass t l
    let B : WordSum R V := colorInsertion l r Y
    let G : WordSum R V := colorClassProduct l Y
    have h₁ : ContextEq f (colorClassProduct (l ++ [r]) (t :: Y))
        ((1 + T) * D * ((1 + B) * G)) := by
      simpa only [colorClassProduct, descendingClass_append, descendingClass, one_mul]
        using ih.mul_left ((1 + T) * D)
    have hkill : ContextEq f (T * D * B * G) 0 := by
      simpa only [T, B, smul_mul_assoc, smul_zero, zero_mul] using
        ((colorInsertion_repeated_root f hrep l r Y D).mul_right G).smul t
    have hcancel : ContextEq f (D * B * I * D * G) (D * B * G) := by
      simpa only [mul_one, mul_assoc] using
        ((inverseClass_mul_descendingClass f hrep t l).mul_left (D * B)).mul_right G
    have heq₁ : (1 + T) * D * ((1 + B) * G) =
        ((1 + T) * D * G + D * B * G) + T * D * B * G := by
      simp only [mul_add, add_mul, one_mul, mul_assoc]
      abel
    have heq₂ : (1 + (T + D * B * I)) * (D * G) =
        (1 + T) * D * G + D * B * I * D * G := by
      simp only [add_mul, one_mul, mul_assoc]
      abel
    have h₂ := (ContextEq.of_eq heq₁).trans ((ContextEq.refl _).add hkill)
    have h₃ := (ContextEq.refl ((1 + T) * D * G)).add hcancel.symm
    have hh : ContextEq f ((1 + T) * D * ((1 + B) * G))
        ((1 + (T + D * B * I)) * (D * G)) := by
      apply ContextEq.trans (B := (1 + T) * D * G + D * B * G)
      · simpa only [add_zero] using h₂
      · exact h₃.trans (ContextEq.of_eq heq₂.symm)
    exact h₁.trans hh

/-- The exact boundary term in the finite shift of a weighted commutator sum. -/
theorem finite_weight_shift (E : ℕ → R) (hE : E 0 = 1) (U : ℕ → WordSum R V)
    (t : R) (N : ℕ) :
    (∑ d ∈ Finset.range N, (E (d + 1) + t * E d) • U d) =
      t • U 0 + (∑ d ∈ Finset.range N, E (d + 1) • (U d + t • U (d + 1))) -
        (t * E N) • U N := by
  have hs : (∑ d ∈ Finset.range N, E d • U d) + E N • U N =
      (∑ d ∈ Finset.range N, E (d + 1) • U (d + 1)) + U 0 := by
    rw [← Finset.sum_range_succ, Finset.sum_range_succ', hE, one_smul]
  have ht := congrArg (fun X : WordSum R V => t • X) hs
  simp only [smul_add, smul_smul] at ht
  have ht' : t • (∑ d ∈ Finset.range N, E d • U d) =
      t • U 0 + t • (∑ d ∈ Finset.range N, E (d + 1) • U (d + 1)) -
        (t * E N) • U N := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using ht
  have hleft : (∑ d ∈ Finset.range N, (E (d + 1) + t * E d) • U d) =
      (∑ d ∈ Finset.range N, E (d + 1) • U d) +
        t • (∑ d ∈ Finset.range N, E d • U d) := by
    simp only [add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  have hright : (∑ d ∈ Finset.range N, E (d + 1) • (U d + t • U (d + 1))) =
      (∑ d ∈ Finset.range N, E (d + 1) • U d) +
        t • (∑ d ∈ Finset.range N, E (d + 1) • U (d + 1)) := by
    simp [smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul, mul_comm]
  rw [hleft, hright, ht']
  abel

end VerticalStripLLT.CyclicHessenberg
