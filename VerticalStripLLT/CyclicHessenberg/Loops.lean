import VerticalStripLLT.CyclicHessenberg.Data
import VerticalStripLLT.Polynomial
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin

/-! The raw cyclic loop/color polynomial, independent of the transfer kernel and expansion. -/

namespace VerticalStripLLT.CyclicHessenberg

open scoped BigOperators

variable {k n m : ℕ}

/-- Canonically labelled loops: the first and last boundary permutations are identities,
and every strand follows an allowed edge. Boundary `n` repeats boundary zero. -/
def IsLoopCover (h : Tuple k n) (L : Fin (n + 1) → Equiv.Perm (Fin k)) : Prop :=
  L 0 = Equiv.refl _ ∧ L (Fin.last n) = Equiv.refl _ ∧
    ∀ (ℓ : Fin n) (a : Fin k), L ℓ.castSucc a ≤ h ℓ (L ℓ.succ a)

/-- A cover is finite layer data satisfying only the original edge conditions. -/
abbrev LoopCover (h : Tuple k n) :=
  {L : Fin (n + 1) → Equiv.Perm (Fin k) // IsLoopCover h L}

noncomputable instance loopCoverFintype (h : Tuple k n) : Fintype (LoopCover h) :=
  Fintype.ofFinite _

/-- Each vertex may stay at its own value in every layer. -/
def identityLoopCover (h : Tuple k n) : LoopCover h :=
  ⟨fun _ => Equiv.refl _, rfl, rfl, fun ℓ a => (h ℓ).le_apply a⟩

instance loopCoverInhabited (h : Tuple k n) : Inhabited (LoopCover h) :=
  ⟨identityLoopCover h⟩

@[simp] theorem loopCover_first (h : Tuple k n) (L : LoopCover h) (a : Fin k) :
    L.val 0 a = a := by rw [L.property.1]; rfl

@[simp] theorem loopCover_last (h : Tuple k n) (L : LoopCover h) (a : Fin k) :
    L.val (Fin.last n) a = a := by rw [L.property.2.1]; rfl

/-- Colors increase; equal colors are ordered by decreasing canonical first-layer labels. -/
def colorPrecedes (κ : Fin k → Fin m) (a b : Fin k) : Prop :=
  κ a < κ b ∨ (κ a = κ b ∧ b < a)

theorem colorPrecedes_of_lt (κ : Fin k → Fin m) {a b : Fin k} (hab : a < b) :
    colorPrecedes κ a b ↔ κ a < κ b := by
  simp [colorPrecedes, not_lt_of_ge (le_of_lt hab)]

theorem colorPrecedes_of_gt (κ : Fin k → Fin m) {a b : Fin k} (hab : b < a) :
    colorPrecedes κ a b ↔ κ a ≤ κ b := by
  simp [colorPrecedes, hab, le_iff_lt_or_eq]

/-- Potential ascent events retain the layer, so parallel occurrences are distinct. -/
noncomputable def loopAscentEvents (h : Tuple k n) (L : LoopCover h) :
    Finset (Fin n × Fin k × Fin k) := by
  classical
  exact Finset.univ.filter fun e =>
    L.val e.1.castSucc e.2.1 < L.val e.1.castSucc e.2.2 ∧
      L.val e.1.castSucc e.2.2 ≤ h e.1 (L.val e.1.succ e.2.1)

/-- The original exponent before the substitution `q ↦ q+1`. -/
noncomputable def coloredLoopAscentCount (h : Tuple k n) (L : LoopCover h)
    (κ : Fin k → Fin m) : ℕ := by
  classical
  exact ((loopAscentEvents h L).filter fun e => colorPrecedes κ e.2.1 e.2.2).card

/-- The independent canonical-cover coloring sum in every finite alphabet.
The source-facing positivity theorem will assume `0 < n`. -/
noncomputable def loopColoringLLT (h : Tuple k n) (m : ℕ) : XPoly m :=
  ∑ L : LoopCover h, ∑ κ : Fin k → Fin m,
    MvPolynomial.C (Polynomial.X ^ coloredLoopAscentCount h L κ) *
      ∏ a : Fin k, MvPolynomial.X (κ a)

instance loopCoverEmptySubsingleton (h : Tuple 0 n) : Subsingleton (LoopCover h) := by
  exact ⟨fun L M => Subtype.ext (Subsingleton.elim _ _)⟩

@[simp] theorem coloredLoopAscentCount_empty (h : Tuple 0 n) (L : LoopCover h)
    (κ : Fin 0 → Fin m) : coloredLoopAscentCount h L κ = 0 := by
  simp [coloredLoopAscentCount, loopAscentEvents]

/-- The unique empty cover and empty coloring have weight one, even for zero colors. -/
@[simp] theorem loopColoringLLT_empty (h : Tuple 0 n) (m : ℕ) :
    loopColoringLLT h m = 1 := by
  classical
  let : Unique (LoopCover h) :=
    ⟨inferInstance, fun L => Subsingleton.elim L default⟩
  simp [loopColoringLLT]

/-- A nonempty vertex set has no coloring in the empty alphabet. -/
@[simp] theorem loopColoringLLT_zero_alphabet (h : Tuple k n) (hk : 0 < k) :
    loopColoringLLT h 0 = 0 := by
  classical
  let : IsEmpty (Fin k → Fin 0) := ⟨fun κ => Fin.elim0 (κ ⟨0, hk⟩)⟩
  simp [loopColoringLLT]

end VerticalStripLLT.CyclicHessenberg
