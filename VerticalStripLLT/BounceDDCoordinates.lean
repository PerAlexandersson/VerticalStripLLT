import VerticalStripLLT.BouncePrefixGeometry
import VerticalStripLLT.PrefixScanners

namespace VerticalStripLLT

open Step

/-- Coordinates for the DN relation with a leading east in the DD induction. -/
theorem BounceSeed.dd_leading_second_coordinates {A V : List Step}
    (h : BounceSeed (A ++ diagonal :: diagonal :: (V ++ [diagonal])))
    (hindex : A.length + 1 = diagonalCount
      (A ++ diagonal :: diagonal :: (V ++ [diagonal]))) :
    (endpointFrom 0 0 A).2 = (endpointFrom 0 0 (A ++ diagonal :: north :: east :: V)).1 ∧
      (endpointFrom 0 0 (A ++ diagonal :: north :: east :: V)).1 + 1 <
        (endpointFrom 0 0 (A ++ diagonal :: north :: east :: V)).2 := by
  have hE : endpointFrom 0 0 (A ++ diagonal :: north :: east :: V) =
      endpointFrom 0 0 (A ++ diagonal :: diagonal :: V) := by
    simp only [endpointFrom_append, endpointFrom]
  rw [hE]
  exact BounceSeed.singleBounce_coordinates A V diagonal diagonal h hindex

/-- A terminal replacement preserving its endpoint gives the second local DN return. -/
theorem BounceSeed.dd_after_ordinary_coordinates {A B V : List Step}
    (h : BounceSeed (A ++ diagonal :: diagonal :: (V ++ [diagonal])))
    (hindex : A.length + 1 = diagonalCount
      (A ++ diagonal :: diagonal :: (V ++ [diagonal])))
    (hB : endpointFrom 0 0 B = endpointFrom 0 0 A) :
    (endpointFrom 0 0 (B ++ [east])).2 =
        (endpointFrom 0 0 ((B ++ [east]) ++ diagonal :: north :: V)).1 ∧
      (endpointFrom 0 0 ((B ++ [east]) ++ diagonal :: north :: V)).1 + 1 <
        (endpointFrom 0 0 ((B ++ [east]) ++ diagonal :: north :: V)).2 := by
  have hy : (endpointFrom 0 0 (B ++ [east])).2 = (endpointFrom 0 0 A).2 := by
    simp only [endpointFrom_append, endpointFrom, hB]
  have hE : endpointFrom 0 0 ((B ++ [east]) ++ diagonal :: north :: V) =
      endpointFrom 0 0 (A ++ diagonal :: diagonal :: V) := by
    simp only [endpointFrom_append, endpointFrom, hB]
  rw [hy, hE]
  exact BounceSeed.singleBounce_coordinates A V diagonal diagonal h hindex

end VerticalStripLLT
