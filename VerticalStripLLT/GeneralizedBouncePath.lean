import VerticalStripLLT.BouncePrefixGeometry
import VerticalStripLLT.ThirdBouncePath

namespace VerticalStripLLT

theorem BounceSeed.valid_swapLast {n : ℕ} {R W : List Step}
    (hseed : BounceSeed (R ++ [Step.diagonal]))
    (h : Step.validFrom n 0 0 (R ++ Step.diagonal :: Step.east :: W) = true) :
    Step.validFrom n 0 0 (R ++ Step.east :: Step.diagonal :: W) = true := by
  apply Step.validFrom_diagonalEast_swap n 0 0 h
  exact hseed.final_gap

theorem BounceSeed.valid_dn_successor {n : ℕ} {U V W : List Step}
    (hseed : BounceSeed ((U ++ Step.diagonal :: Step.north :: V) ++ [Step.diagonal]))
    (h : Step.validFrom n 0 0
      ((U ++ Step.diagonal :: Step.north :: V) ++
        Step.diagonal :: Step.east :: W) = true) :
    Step.validFrom n 0 0
      ((U ++ Step.north :: Step.diagonal :: V) ++
        Step.east :: Step.diagonal :: W) = true := by
  exact (SchroderPath.secondBounceSuccessor U V W h hseed.final_gap).valid

theorem BounceDecomposition.valid_nd_successor {n : ℕ} {Y U V W : List Step}
    (hD : BounceDecomposition Y U V Step.north Step.diagonal)
    (hseed : BounceSeed Y)
    (h : Step.validFrom n 0 0
      ((U ++ Step.north :: Step.diagonal :: V) ++
        Step.diagonal :: Step.east :: W) = true) :
    Step.validFrom n 0 0
      ((U ++ Step.diagonal :: Step.north :: V) ++
        Step.east :: Step.diagonal :: W) = true := by
  have hs : BounceSeed ((U ++ Step.north :: Step.diagonal :: V) ++ [Step.diagonal]) := by
    rw [hD.word_eq] at hseed
    simpa only [List.append_assoc, List.cons_append] using hseed
  have hQ := hs.valid_swapLast h
  have hQ' : Step.validFrom n 0 0
      (U ++ Step.north :: Step.diagonal :: (V ++ Step.east :: Step.diagonal :: W)) =
      true := by
    simpa only [List.append_assoc, List.cons_append] using hQ
  simpa only [List.append_assoc, List.cons_append] using
    Step.validFrom_northDiagonal_swap n 0 0 hQ' (hD.corner_lt (Or.inr rfl))

end VerticalStripLLT
