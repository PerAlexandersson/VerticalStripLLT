import VerticalStripLLT.FirstEast
import VerticalStripLLT.PrefixScanners

namespace VerticalStripLLT

namespace Step

theorem eastCount_diagonalEast_swap (R W : List Step) :
    eastCount (R ++ diagonal :: east :: W) =
      eastCount (R ++ east :: diagonal :: W) := by
  simp [eastCount]

theorem firstEastHeight_diagonalEast_swap (R W : List Step)
    (hR : east ∉ R) :
    firstEastHeight (R ++ diagonal :: east :: W) =
      firstEastHeight (R ++ east :: diagonal :: W) + 1 := by
  have hs := firstEastHeight_append_east (R ++ [diagonal]) W (by simpa using hR)
  have ht := firstEastHeight_append_east R (diagonal :: W) hR
  simp only [List.append_assoc, List.singleton_append] at hs ht ⊢
  rw [hs, ht]
  simp [endpointFrom_append, endpointFrom]

end Step
end VerticalStripLLT
