import VerticalStripLLT.Components.MountainCoefficients

/-! Repeated indices vanish in products of squarefree noncommuting generators. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {I R : Type*} [Ring R]

theorem list_prod_eq_zero_of_not_nodup (u : I → R)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (L : List I) (hL : ¬L.Nodup) : (L.map u).prod = 0 := by
  classical
  induction L with
  | nil => exact (hL List.nodup_nil).elim
  | cons a L ih =>
    by_cases ha : a ∈ L
    · obtain ⟨P, S, rfl⟩ := List.append_of_mem ha
      simp only [List.map_cons, List.map_append, List.prod_cons, List.prod_append]
      calc
        u a * ((P.map u).prod * (u a * (S.map u).prod)) =
            (u a * (P.map u).prod * u a) * (S.map u).prod := by
          simp only [mul_assoc]
        _ = 0 := by rw [squarefree, zero_mul]
    · have hn : ¬L.Nodup := fun h => hL (List.nodup_cons.mpr ⟨ha, h⟩)
      simp only [List.map_cons, List.prod_cons, ih hn, mul_zero]

/-- A shared index on the two sides kills the whole mountain term. -/
theorem mountain_product_eq_zero_of_overlap (u : I → R)
    (squarefree : ∀ i (Y : R), u i * Y * u i = 0)
    (L S : List I) (r : I) (h : ∃ a, a ∈ L ∧ a ∈ S) :
    (L.map u).prod * u r * (S.map u).prod = 0 := by
  have hn : ¬(L ++ [r] ++ S).Nodup := by
    intro hd
    obtain ⟨a, haL, haS⟩ := h
    have hdis := (List.nodup_append.mp hd).2.2
    exact hdis a (List.mem_append_left _ haL) a haS rfl
  have hz := list_prod_eq_zero_of_not_nodup u squarefree (L ++ [r] ++ S) hn
  simpa only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one] using hz

end

end VerticalStripLLT.Components
