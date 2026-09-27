import VerticalStripLLT.Components.BlockWordSupport
import VerticalStripLLT.Components.ComponentWords

/-! Full-word criteria for flattened mountain blocks. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {V : Type*} [LinearOrder V]

/-- Every mountain block word is a nodup list. -/
theorem blockWord_nodup (B T : Finset V) (hT : T ⊆ B) :
    (blockWord B T).Nodup := by
  have hinc : (incWord (B \ T)).Nodup := by
    simpa [incWord] using (B \ T).sort_nodup (· ≤ ·)
  have hdec : (decWord T).Nodup := by
    simpa [decWord] using T.sort_nodup (· ≥ ·)
  have hdis : List.Disjoint (incWord (B \ T)) (decWord T) := by
    intro v hvinc hvdec
    have hvinc' : v ∈ B \ T := by simpa [incWord] using hvinc
    have hvdec' : v ∈ T := by simpa [decWord] using hvdec
    exact (Finset.mem_sdiff.mp hvinc').2 hvdec'
  exact List.Nodup.append hinc hdec hdis

private theorem blockWord_disjoint_iff
    (B C : Finset V) (T : Finset V) (U : Finset V)
    (hT : T ⊆ B) (hU : U ⊆ C) :
    List.Disjoint (blockWord B T) (blockWord C U) ↔ Disjoint B C := by
  constructor
  · intro h
    rw [Finset.disjoint_left]
    intro v hvB hvC
    apply h
    · exact (mem_blockWord_iff B T hT v).mpr hvB
    · exact (mem_blockWord_iff C U hU v).mpr hvC
  · intro h v hvB hvC
    exact (Finset.disjoint_left.mp h)
      ((mem_blockWord_iff B T hT v).mp hvB)
      ((mem_blockWord_iff C U hU v).mp hvC)

/-- The flattened block word is full precisely when the carriers are pairwise
disjoint and cover every vertex. -/
theorem fullWord_blockWords_flatten_iff
    (blocks : List (Finset V × Finset V))
    (hsub : ∀ BT ∈ blocks, BT.2 ⊆ BT.1) :
    fullWord ((blocks.map (fun BT => blockWord BT.1 BT.2)).flatten) ↔
      (blocks.Pairwise (fun B C => Disjoint B.1 C.1) ∧
        ∀ v, ∃ BT ∈ blocks, v ∈ BT.1) := by
  let words : List (List V) :=
    blocks.map (fun BT => blockWord BT.1 BT.2)
  have hword_nodup : ∀ W ∈ words, W.Nodup := by
    intro W hW
    obtain ⟨BT, hBT, rfl⟩ := List.mem_map.mp hW
    exact blockWord_nodup BT.1 BT.2 (hsub BT hBT)
  have hpair_iff :
      (blocks.map (fun BT => blockWord BT.1 BT.2)).Pairwise List.Disjoint ↔
        blocks.Pairwise (fun B C => Disjoint B.1 C.1) := by
    rw [List.pairwise_map]
    constructor
    · intro h
      exact h.imp_of_mem fun {B C} hB hC hd =>
        (blockWord_disjoint_iff B.1 C.1 B.2 C.2 (hsub B hB) (hsub C hC)).mp hd
    · intro h
      exact h.imp_of_mem fun {B C} hB hC hd =>
        (blockWord_disjoint_iff B.1 C.1 B.2 C.2 (hsub B hB) (hsub C hC)).mpr hd
  have hflatten_nodup : words.flatten.Nodup ↔ words.Pairwise List.Disjoint := by
    rw [List.nodup_flatten]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨hword_nodup, h⟩
  change fullWord words.flatten ↔ _
  change (words.flatten.Nodup ∧ ∀ v, v ∈ words.flatten) ↔ _
  constructor
  · rintro ⟨hnodup, hcover⟩
    refine ⟨(by simpa [words] using hpair_iff.mp (hflatten_nodup.mp hnodup)), ?_⟩
    intro v
    obtain ⟨W, hW, hvW⟩ := List.mem_flatten.mp (hcover v)
    obtain ⟨BT, hBT, hWBT⟩ := List.mem_map.mp hW
    refine ⟨BT, hBT, ?_⟩
    have hvBlock : v ∈ blockWord BT.1 BT.2 := by
      simpa [hWBT] using hvW
    exact (mem_blockWord_iff BT.1 BT.2 (hsub BT hBT) v).mp hvBlock
  · rintro ⟨hpair, hcover⟩
    have hpair' : words.Pairwise List.Disjoint :=
      hpair_iff.mpr (by simpa [words] using hpair)
    refine ⟨hflatten_nodup.mpr hpair', ?_⟩
    intro v
    obtain ⟨BT, hBT, hvBT⟩ := hcover v
    apply List.mem_flatten.mpr
    refine ⟨blockWord BT.1 BT.2, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨BT, hBT, rfl⟩
    · exact (mem_blockWord_iff BT.1 BT.2 (hsub BT hBT) v).mpr hvBT

end

end VerticalStripLLT.Components
