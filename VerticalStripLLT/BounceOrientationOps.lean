import VerticalStripLLT.BounceHRVCore
-- Local helper module: VerticalStripLLT.BounceOrientationOps

/-! ## Orientation operations on the common background -/

namespace VerticalStripLLT
namespace BounceHRV

open scoped BigOperators

variable {n : ℕ}

section OrientationOps

variable {B : SchroderPath n} {i y : Fin n}

/-- Reset the orientation bit of the normal edge `(i,y)`. -/
def setBit (i y : Fin n) (β : Bool) (θ : Orientation B) : Orientation B :=
  fun e => if e.1 = (i, y) then β else θ e

/-- The orientation bit of the normal edge `(i,y)`. -/
def bitOf (hiy : (i, y) ∈ B.normalEdges) (θ : Orientation B) : Bool := θ ⟨(i, y), hiy⟩

variable (hNinv : (B.normalEdges.erase (i, y)).map (swapVertexPair i y) =
  B.normalEdges.erase (i, y))

/-- Exchange the vertices `i,y` on all normal edges other than `(i,y)`. -/
def swapEdgeFun (e : {e // e ∈ B.normalEdges}) : {e // e ∈ B.normalEdges} :=
  if h : e.1 = (i, y) then e else
    ⟨swapVertexPair i y e.1, Finset.mem_of_mem_erase
      (mem_of_map_swapVertexPair_eq i y hNinv (Finset.mem_erase.2 ⟨h, e.2⟩))⟩

theorem swapEdgeFun_val_ne {e : {e // e ∈ B.normalEdges}} (h : e.1 ≠ (i, y)) :
    (swapEdgeFun hNinv e).1 ≠ (i, y) := by
  unfold swapEdgeFun
  rw [dite_eq_right h]
  exact (Finset.mem_erase.1
    (mem_of_map_swapVertexPair_eq i y hNinv (Finset.mem_erase.2 ⟨h, e.2⟩))).1

theorem swapEdgeFun_val {e : {e // e ∈ B.normalEdges}} (h : e.1 ≠ (i, y)) :
    (swapEdgeFun hNinv e).1 = swapVertexPair i y e.1 := by
  unfold swapEdgeFun
  rw [dite_eq_right h]

theorem swapEdgeFun_involutive : Function.Involutive (swapEdgeFun hNinv) := by
  intro e
  by_cases h : e.1 = (i, y)
  · unfold swapEdgeFun; rw [dite_eq_left h, dite_eq_left h]
  · have h' := swapEdgeFun_val_ne hNinv h
    apply Subtype.ext
    rw [swapEdgeFun_val hNinv h', swapEdgeFun_val hNinv h]
    simp [swapVertexPair_apply]

/-- The vertex swap, as a permutation of the normal edges of the background. -/
def swapEdge : Equiv.Perm {e // e ∈ B.normalEdges} :=
  Function.Involutive.toPerm _ (swapEdgeFun_involutive hNinv)

/-- The swapped orientation. -/
def swapO (θ : Orientation B) : Orientation B := fun e => θ (swapEdge hNinv e)

theorem swapO_apply_of_ne (θ : Orientation B) {u w : Fin n} (hu : (u, w) ∈ B.normalEdges)
    (h : (u, w) ≠ (i, y)) :
    swapO hNinv θ ⟨(u, w), hu⟩ = θ ⟨(Equiv.swap i y u, Equiv.swap i y w), by
      have := (swapEdge hNinv ⟨(u, w), hu⟩).2
      simpa [swapEdge, swapEdgeFun, h, swapVertexPair_apply] using this⟩ := by
  simp [swapO, swapEdge, swapEdgeFun, h, swapVertexPair_apply]

theorem orientationAsc_swapO (θ : Orientation B) :
    orientationAsc B (swapO hNinv θ) = orientationAsc B θ := by
  unfold orientationAsc swapO
  refine Finset.card_bij (fun e _ => swapEdge hNinv e) ?_ ?_ ?_
  · intro e he
    simpa using he
  · intro a _ b _ hab
    exact (swapEdge hNinv).injective hab
  · intro e he
    refine ⟨swapEdge hNinv e, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      rw [show swapEdge hNinv (swapEdge hNinv e) = e from swapEdgeFun_involutive hNinv e]
      exact he
    · exact swapEdgeFun_involutive hNinv e

end OrientationOps

section BitOps

variable {B : SchroderPath n} {i y : Fin n} (hiy : (i, y) ∈ B.normalEdges)

theorem orientationAsc_setBit (β : Bool) (θ : Orientation B) :
    orientationAsc B (setBit i y β θ) + (if bitOf hiy θ then 1 else 0) =
      orientationAsc B θ + (if β then 1 else 0) := by
  classical
  unfold orientationAsc
  simp only [Finset.card_filter]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨(i, y), hiy⟩ : {e // e ∈ B.normalEdges})),
    ← Finset.add_sum_erase _ (fun e => if θ e = true then 1 else 0)
      (Finset.mem_univ (⟨(i, y), hiy⟩ : {e // e ∈ B.normalEdges}))]
  have hrest : ∑ x ∈ Finset.univ.erase (⟨(i, y), hiy⟩ : {e // e ∈ B.normalEdges}),
      (if setBit i y β θ x = true then 1 else 0) =
      ∑ x ∈ Finset.univ.erase (⟨(i, y), hiy⟩ : {e // e ∈ B.normalEdges}),
      (if θ x = true then 1 else 0) := by
    refine Finset.sum_congr rfl fun e he => ?_
    have hne : e.1 ≠ (i, y) := fun h => (Finset.mem_erase.1 he).1 (Subtype.ext h)
    simp [setBit, hne]
  rw [hrest]
  have h0 : setBit i y β θ ⟨(i, y), hiy⟩ = β := by simp [setBit]
  rw [h0]
  simp only [bitOf]
  ac_rfl

theorem bitOf_setBit (β : Bool) (θ : Orientation B) : bitOf hiy (setBit i y β θ) = β := by
  simp [bitOf, setBit]

theorem setBit_bitOf (θ : Orientation B) : setBit i y (bitOf hiy θ) θ = θ := by
  funext e
  by_cases h : e.1 = (i, y)
  · have : e = ⟨(i, y), hiy⟩ := Subtype.ext h
    subst this
    simp [setBit, bitOf]
  · simp [setBit, h]

theorem setBit_setBit (β β' : Bool) (θ : Orientation B) :
    setBit i y β (setBit i y β' θ) = setBit i y β θ := by
  funext e
  by_cases h : e.1 = (i, y) <;> simp [setBit, h]

variable (hNinv : (B.normalEdges.erase (i, y)).map (swapVertexPair i y) =
  B.normalEdges.erase (i, y))

theorem swapEdge_val_eq_iff (e : {e // e ∈ B.normalEdges}) :
    (swapEdge hNinv e).1 = (i, y) ↔ e.1 = (i, y) := by
  constructor
  · intro h
    by_contra hne
    exact swapEdgeFun_val_ne hNinv hne h
  · intro h
    simp [swapEdge, swapEdgeFun, h]

theorem bitOf_swapO (θ : Orientation B) : bitOf hiy (swapO hNinv θ) = bitOf hiy θ := by
  simp [bitOf, swapO, swapEdge, swapEdgeFun]

theorem swapO_setBit (β : Bool) (θ : Orientation B) :
    swapO hNinv (setBit i y β θ) = setBit i y β (swapO hNinv θ) := by
  funext e
  simp only [swapO, setBit, swapEdge_val_eq_iff]

theorem swapO_swapO (θ : Orientation B) : swapO hNinv (swapO hNinv θ) = θ := by
  funext e
  simp only [swapO]
  rw [show swapEdge hNinv (swapEdge hNinv e) = e from swapEdgeFun_involutive hNinv e]

end BitOps

end BounceHRV
end VerticalStripLLT

