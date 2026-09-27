import VerticalStripLLT.Components.BlockExtractor
import Mathlib.Data.Finset.Image

/-! Transport of sorted block words along order embeddings. -/

namespace VerticalStripLLT.Components

open Classical

noncomputable section

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

theorem incWord_map_orderEmbedding (e : α ↪o β) (s : Finset α) :
    incWord (s.map e.toEmbedding) = (incWord s).map e := by
  simpa [incWord] using
    (Finset.map_sort e.toEmbedding s (· ≤ ·) (· ≤ ·)
      (fun a _ b _ => (e.le_iff_le : e a ≤ e b ↔ a ≤ b).symm)).symm

theorem decWord_map_orderEmbedding (e : α ↪o β) (s : Finset α) :
    decWord (s.map e.toEmbedding) = (decWord s).map e := by
  simpa [decWord] using
    (Finset.map_sort e.toEmbedding s (· ≥ ·) (· ≥ ·)
      (fun a _ b _ => (e.le_iff_le : e b ≤ e a ↔ b ≤ a).symm)).symm

theorem blockWord_map_orderEmbedding (e : α ↪o β)
    (B T : Finset α) :
    blockWord (B.map e.toEmbedding) (T.map e.toEmbedding) =
      (blockWord B T).map e := by
  simp only [blockWord, ← Finset.map_sdiff, incWord_map_orderEmbedding,
    decWord_map_orderEmbedding, List.map_append]

end

end VerticalStripLLT.Components
