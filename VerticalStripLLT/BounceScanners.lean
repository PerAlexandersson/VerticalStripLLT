import VerticalStripLLT.PrefixScanners
import VerticalStripLLT.PathBounds

namespace VerticalStripLLT
namespace Step

theorem endpointFrom_mono (x y : ℕ) (w : List Step) :
    x ≤ (endpointFrom x y w).1 ∧ y ≤ (endpointFrom x y w).2 := by
  induction w generalizing x y with
  | nil => simp [endpointFrom]
  | cons s w ih =>
      cases s
      · have := ih x (y + 1); simp only [endpointFrom]; lia
      · have := ih (x + 1) (y + 1); simp only [endpointFrom]; lia
      · have := ih (x + 1) y; simp only [endpointFrom]; lia

theorem normalFrom_endpoint_bounds (x y u v : ℕ) {w : List Step}
    (h : normalFrom x y u v w = true) :
    u < (endpointFrom x y w).1 ∧ v < (endpointFrom x y w).2 := by
  induction w generalizing x y with
  | nil => simp [normalFrom] at h
  | cons s w ih =>
      cases s <;>
        simp only [normalFrom, endpointFrom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at h ⊢
      · exact ih x (y + 1) h
      · rcases h with h | h
        · have := endpointFrom_mono (x + 1) (y + 1) w; lia
        · exact ih (x + 1) (y + 1) h
      · rcases h with h | h
        · have := endpointFrom_mono (x + 1) y w; lia
        · exact ih (x + 1) y h

theorem strictFrom_endpoint_bounds (x y u v : ℕ) {w : List Step}
    (h : strictFrom x y u v w = true) :
    u < (endpointFrom x y w).1 ∧ v < (endpointFrom x y w).2 ∧ y ≤ v := by
  induction w generalizing x y with
  | nil => simp [strictFrom] at h
  | cons s w ih =>
      cases s <;>
        simp only [strictFrom, endpointFrom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h ⊢
      · have := ih x (y + 1) h; lia
      · rcases h with h | h
        · have := endpointFrom_mono (x + 1) (y + 1) w; lia
        · have := ih (x + 1) (y + 1) h; lia
      · exact ih (x + 1) y h

theorem normalFrom_retarget (x y u v v' : ℕ) {w : List Step}
    (h : normalFrom x y u v w = true) (hu : u < v') (hv : v' < y) :
    normalFrom x y u v' w = true := by
  induction w generalizing x y with
  | nil => simp [normalFrom] at h
  | cons s w ih =>
      cases s <;>
        simp only [normalFrom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at h ⊢
      · exact ih x (y + 1) h (by lia)
      · rcases h with h | h
        · left; lia
        · exact Or.inr (ih (x + 1) (y + 1) h (by lia))
      · rcases h with h | h
        · left; lia
        · exact Or.inr (ih (x + 1) y h hv)

theorem normalFrom_start_le (x y u v : ℕ) {w : List Step}
    (h : normalFrom x y u v w = true) : x ≤ u ∧ u < v :=
  ⟨normalFrom_lower_bound x y u v h, normalFrom_lt x y u v h⟩
/-- Swap of the two values `i` and `i+1` on natural-number labels. -/
def swapNat (i x : ℕ) : ℕ := if x = i then i + 1 else if x = i + 1 then i else x

theorem normalFrom_firstBounce_split (U V W : List Step) (a b : ℕ) :
    normalFrom 0 0 a b ((U ++ north :: north :: V) ++ east :: east :: north :: W) = true ↔
      normalFrom 0 0 a b U = true ∨
      normalFrom (endpointFrom 0 0 U).1 ((endpointFrom 0 0 U).2 + 2) a b V = true ∨
      (a = (endpointFrom 0 0 (U ++ north :: north :: V)).1 ∧
        (endpointFrom 0 0 (U ++ north :: north :: V)).1 < b ∧
        b < (endpointFrom 0 0 (U ++ north :: north :: V)).2) ∨
      (a = (endpointFrom 0 0 (U ++ north :: north :: V)).1 + 1 ∧
        (endpointFrom 0 0 (U ++ north :: north :: V)).1 + 1 < b ∧
        b < (endpointFrom 0 0 (U ++ north :: north :: V)).2) ∨
      normalFrom ((endpointFrom 0 0 (U ++ north :: north :: V)).1 + 2)
        ((endpointFrom 0 0 (U ++ north :: north :: V)).2 + 1) a b W = true := by
  rw [normalFrom_append, normalFrom_append]
  simp only [normalFrom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    and_assoc, or_assoc, Nat.add_assoc, Nat.reduceAdd]

theorem strictFrom_firstBounce_split (U V W : List Step) (a b : ℕ) :
    strictFrom 0 0 a b ((U ++ north :: north :: V) ++ east :: east :: north :: W) = true ↔
      strictFrom 0 0 a b U = true ∨
      strictFrom (endpointFrom 0 0 U).1 ((endpointFrom 0 0 U).2 + 2) a b V = true ∨
      strictFrom ((endpointFrom 0 0 (U ++ north :: north :: V)).1 + 2)
        ((endpointFrom 0 0 (U ++ north :: north :: V)).2 + 1) a b W = true := by
  rw [strictFrom_append, strictFrom_append]
  simp only [strictFrom, Bool.or_eq_true, or_assoc, Nat.add_assoc]

end Step
end VerticalStripLLT

namespace VerticalStripLLT
namespace Step

theorem swapNat_of_ne (i x : ℕ) (h1 : x ≠ i) (h2 : x ≠ i + 1) : swapNat i x = x := by
  unfold swapNat; rw [ite_eq_right h1, ite_eq_right h2]

theorem endpointFrom_firstBounce (U V : List Step) :
    endpointFrom 0 0 (U ++ north :: north :: V) =
      endpointFrom (endpointFrom 0 0 U).1 ((endpointFrom 0 0 U).2 + 2) V := by
  rw [endpointFrom_append]
  simp only [endpointFrom, Nat.add_assoc, Nat.reduceAdd]

theorem normalFrom_firstBounce_swap (U V W : List Step)
    (hreturn : (endpointFrom 0 0 U).2 = (endpointFrom 0 0 (U ++ north :: north :: V)).1)
    (a b : ℕ)
    (h : normalFrom 0 0 a b ((U ++ north :: north :: V) ++ east :: east :: north :: W) = true)
    (hne : ¬(a = (endpointFrom 0 0 (U ++ north :: north :: V)).1 ∧
      b = (endpointFrom 0 0 (U ++ north :: north :: V)).1 + 1)) :
    normalFrom 0 0 (swapNat (endpointFrom 0 0 (U ++ north :: north :: V)).1 a)
      (swapNat (endpointFrom 0 0 (U ++ north :: north :: V)).1 b)
      ((U ++ north :: north :: V) ++ east :: east :: north :: W) = true := by
  have hR := endpointFrom_firstBounce U V
  rw [normalFrom_firstBounce_split] at h ⊢
  generalize hi : (endpointFrom 0 0 (U ++ north :: north :: V)).1 = i at *
  generalize hj : (endpointFrom 0 0 (U ++ north :: north :: V)).2 = j at *
  have hmono := endpointFrom_mono (endpointFrom 0 0 U).1 ((endpointFrom 0 0 U).2 + 2) V
  rw [← hR, hi, hj] at hmono
  rcases h with h | h | h | h | h
  · have hb := normalFrom_endpoint_bounds 0 0 a b h
    left
    rw [swapNat_of_ne i a (by lia) (by lia), swapNat_of_ne i b (by lia) (by lia)]
    exact h
  · have hb := normalFrom_endpoint_bounds _ _ a b h
    rw [← hR, hi, hj] at hb
    right; left
    rw [swapNat_of_ne i a (by lia) (by lia)]
    have hab := normalFrom_lt _ _ a b h
    by_cases hb1 : b = i
    · subst hb1
      simp only [swapNat, ite_true]
      exact normalFrom_retarget _ _ a _ _ h (by lia) (by lia)
    by_cases hb2 : b = i + 1
    · subst hb2
      simp only [swapNat, ite_eq_right (show i + 1 ≠ i by lia), ite_true]
      exact normalFrom_retarget _ _ a _ _ h (by lia) (by lia)
    rw [swapNat_of_ne i b hb1 hb2]
    exact h
  · right; right; right; left
    have hb2 : b ≠ i + 1 := fun hb => hne ⟨h.1, hb⟩
    rw [h.1, swapNat_of_ne i b (by lia) hb2]
    simp only [swapNat, ite_true]
    exact ⟨trivial, by lia, by lia⟩
  · right; right; left
    rw [h.1, swapNat_of_ne i b (by lia) (by lia)]
    simp only [swapNat, ite_eq_right (show i + 1 ≠ i by lia), ite_true]
    exact ⟨trivial, by lia, by lia⟩
  · have hb := normalFrom_start_le _ _ a b h
    right; right; right; right
    rw [swapNat_of_ne i a (by lia) (by lia), swapNat_of_ne i b (by lia) (by lia)]
    exact h

theorem strictFrom_firstBounce_fixed (U V W : List Step)
    (hreturn : (endpointFrom 0 0 U).2 = (endpointFrom 0 0 (U ++ north :: north :: V)).1)
    (a b : ℕ)
    (h : strictFrom 0 0 a b ((U ++ north :: north :: V) ++ east :: east :: north :: W) = true) :
    swapNat (endpointFrom 0 0 (U ++ north :: north :: V)).1 a = a ∧
      swapNat (endpointFrom 0 0 (U ++ north :: north :: V)).1 b = b := by
  have hR := endpointFrom_firstBounce U V
  rw [strictFrom_firstBounce_split] at h
  generalize hi : (endpointFrom 0 0 (U ++ north :: north :: V)).1 = i at *
  generalize hj : (endpointFrom 0 0 (U ++ north :: north :: V)).2 = j at *
  have hmono := endpointFrom_mono (endpointFrom 0 0 U).1 ((endpointFrom 0 0 U).2 + 2) V
  rw [← hR, hi, hj] at hmono
  have hW := endpointFrom_mono (i + 2) (j + 1) W
  rcases h with h | h | h
  · have hb := strictFrom_endpoint_bounds 0 0 a b h
    exact ⟨swapNat_of_ne i a (by lia) (by lia), swapNat_of_ne i b (by lia) (by lia)⟩
  · have hb := strictFrom_endpoint_bounds _ _ a b h
    rw [← hR, hi, hj] at hb
    exact ⟨swapNat_of_ne i a (by lia) (by lia), swapNat_of_ne i b (by lia) (by lia)⟩
  · have hb := strictFrom_endpoint_bounds _ _ a b h
    have hl := strictFrom_lower_bound _ _ a b h
    exact ⟨swapNat_of_ne i a (by lia) (by lia), swapNat_of_ne i b (by lia) (by lia)⟩

end Step
end VerticalStripLLT
