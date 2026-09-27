import VerticalStripLLT.Components.BlockWordCompatibility

/-! Support and flattened compatibility for finite mountain blocks. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {V : Type*} [LinearOrder V]

/-- A block word has exactly the same membership predicate as its carrier. -/
theorem mem_blockWord_iff (B T : Finset V) (hT : T ⊆ B) (v : V) :
    v ∈ blockWord B T ↔ v ∈ B := by
  simp only [blockWord, List.mem_append]
  constructor
  · intro hv
    rcases hv with hv | hv
    · have hv' : v ∈ B \ T := by simpa [incWord] using hv
      exact (Finset.mem_sdiff.mp hv').1
    · have hv' : v ∈ T := by simpa [decWord] using hv
      exact hT hv'
  · intro hv
    by_cases hvT : v ∈ T
    · exact Or.inr (by simpa [decWord] using hvT)
    · exact Or.inl (by simpa [incWord] using Finset.mem_sdiff.mpr ⟨hv, hvT⟩)

/-- Flattened block words are compatible exactly when each block is compatible
and every edge points from an earlier block to a later block. -/
theorem wordCompatible_blockWords_flatten_iff
    (R : V → V → Prop) (blocks : List (Finset V × Finset V))
    (hsub : ∀ BT ∈ blocks, BT.2 ⊆ BT.1) :
    wordCompatible R
        ((blocks.map (fun BT => blockWord BT.1 BT.2)).flatten) ↔
      ((∀ BT ∈ blocks, wordCompatible R (blockWord BT.1 BT.2)) ∧
        blocks.Pairwise
          (fun B C => ∀ u ∈ B.1, ∀ v ∈ C.1, ¬ R v u)) := by
  induction blocks with
  | nil => simp [wordCompatible]
  | cons BT blocks ih =>
      have hBT : BT.2 ⊆ BT.1 := hsub BT (by simp)
      have hsub_tail : ∀ BC ∈ blocks, BC.2 ⊆ BC.1 := by
        intro BC hBC
        exact hsub BC (by simp [hBC])
      have ih' := ih hsub_tail
      rw [List.map_cons, List.flatten_cons, wordCompatible_append_iff, ih']
      constructor
      · rintro ⟨hBTcompat, ⟨htailcompat, hpwtail⟩, hcross⟩
        refine ⟨?_, ?_⟩
        · intro BC hBC
          rcases List.mem_cons.mp hBC with rfl | hBC
          · exact hBTcompat
          · exact htailcompat BC hBC
        · rw [List.pairwise_cons]
          refine ⟨?_, hpwtail⟩
          intro BC hBC u hu v hv hvu
          have hu' : u ∈ blockWord BT.1 BT.2 :=
            (mem_blockWord_iff BT.1 BT.2 hBT u).mpr hu
          have hv' : v ∈ blockWord BC.1 BC.2 :=
            (mem_blockWord_iff BC.1 BC.2 (hsub_tail BC hBC) v).mpr hv
          have hvflat : v ∈
              (blocks.map (fun B => blockWord B.1 B.2)).flatten := by
            apply List.mem_flatten.mpr
            refine ⟨blockWord BC.1 BC.2, ?_, hv'⟩
            exact List.mem_map.mpr ⟨BC, hBC, rfl⟩
          exact hcross u hu' v hvflat hvu
      · rintro ⟨hall, hcrossBlocks⟩
        have hBTcompat := hall BT (by simp)
        have htailcompat :
            ∀ BC ∈ blocks, wordCompatible R (blockWord BC.1 BC.2) := by
          intro BC hBC
          exact hall BC (by simp [hBC])
        refine ⟨hBTcompat, ⟨htailcompat, (List.pairwise_cons.mp hcrossBlocks).2⟩, ?_⟩
        intro u hu v hv hvu
        obtain ⟨W, hW, hvBC⟩ := List.mem_flatten.mp hv
        obtain ⟨BC, hBC, rfl⟩ := List.mem_map.mp hW
        have hcrossBC := (List.pairwise_cons.mp hcrossBlocks).1 BC hBC
        have huB : u ∈ BT.1 :=
          (mem_blockWord_iff BT.1 BT.2 hBT u).mp hu
        have hvB : v ∈ BC.1 :=
          (mem_blockWord_iff BC.1 BC.2 (hsub_tail BC hBC) v).mp hvBC
        exact hcrossBC u huB v hvB hvu

end

end VerticalStripLLT.Components
