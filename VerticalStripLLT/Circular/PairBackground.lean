import VerticalStripLLT.SwapSum

/-! Finite-set bookkeeping for the normal background of an NN bounce. -/

namespace VerticalStripLLT.Circular

theorem normal_background_swap {n : ℕ} (E S : Finset (Fin n × Fin n))
    (i y z : Fin n) (he : (i, z) ∈ S) (hzi : z ≠ i) (hzy : z ≠ y)
    (hE : (E.erase (i, y)).map (swapVertexPair i y) = E.erase (i, y))
    (hS : (S.erase (i, z)).map (swapVertexPair i y) = S.erase (i, z)) :
    (((E \ S).erase (y, z)).erase (i, y)).map (swapVertexPair i y) =
      ((E \ S).erase (y, z)).erase (i, y) := by
  classical
  have hfixed : (insert (y, z) S).map (swapVertexPair i y) = insert (y, z) S := by
    have hd : insert (y, z) S = insert (y, z) (insert (i, z) (S.erase (i, z))) := by
      rw [Finset.insert_erase he]
    rw [hd, Finset.map_insert, Finset.map_insert, hS]
    simp only [swapVertexPair_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hzi hzy]
    exact Finset.insert_comm _ _ _
  have hrewrite : ((E \ S).erase (y, z)).erase (i, y) =
      E.erase (i, y) \ insert (y, z) S := by
    ext a
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
    tauto
  rw [hrewrite, Finset.map_sdiff, hE, hfixed]

end VerticalStripLLT.Circular
