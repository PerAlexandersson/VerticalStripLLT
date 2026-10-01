import VerticalStripLLT.Components.DiagramProof.RelationalValues
import VerticalStripLLT.Components.DiagramProof.DiagramMeasure
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Signed combinations of whole components

A recurrence of the diagram proof expresses one whole component as an integer
combination of whole components, with the same coefficients for the strict
coloring value `K` and the HRV value `E`. We record such combinations as
finitely supported integer functions on whole components and evaluate them by
linear maps. The values fix the colour of the greatest vertex.

A flip-closed set of states is the disjoint union of the whole components of
chosen representatives, so its value sum is a combination of whole components.
-/

set_option backward.isDefEq.respectTransparency false

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- A whole component: a forward diagram on `Fin (k+1)` and one of its states. -/
structure Comp (k : ℕ) where
  D : Diagram (k + 1)
  forward : Forward D
  θ : Orientation D

namespace Comp

variable {k : ℕ}

/-- The right-marked strict-coloring value of the whole component. -/
def K (x : Comp k) (m : ℕ) (β : Fin m) : XPoly m := componentMarkedK x.θ (Fin.last k) m β

/-- The right-marked HRV value of the whole component. -/
def E (x : Comp k) (m : ℕ) (β : Fin m) : XPoly m := componentMarkedE x.θ (Fin.last k) m β

end Comp

/-- Integer combinations of whole components. -/
abbrev Cert (k : ℕ) := Comp k →₀ ℤ

namespace Cert

variable {k : ℕ}

/-- The right-marked strict-coloring value of a combination. -/
def K (c : Cert k) (m : ℕ) (β : Fin m) : XPoly m :=
  Finsupp.linearCombination ℤ (fun x : Comp k => x.K m β) c

/-- The right-marked HRV value of a combination. -/
def E (c : Cert k) (m : ℕ) (β : Fin m) : XPoly m :=
  Finsupp.linearCombination ℤ (fun x : Comp k => x.E m β) c

@[simp] theorem K_single (x : Comp k) (z : ℤ) (m : ℕ) (β : Fin m) :
    Cert.K (Finsupp.single x z) m β = z • x.K m β :=
  Finsupp.linearCombination_single ..

@[simp] theorem E_single (x : Comp k) (z : ℤ) (m : ℕ) (β : Fin m) :
    Cert.E (Finsupp.single x z) m β = z • x.E m β :=
  Finsupp.linearCombination_single ..

@[simp] theorem K_add (c d : Cert k) (m : ℕ) (β : Fin m) :
    Cert.K (c + d) m β = Cert.K c m β + Cert.K d m β :=
  map_add ..

@[simp] theorem E_add (c d : Cert k) (m : ℕ) (β : Fin m) :
    Cert.E (c + d) m β = Cert.E c m β + Cert.E d m β :=
  map_add ..

@[simp] theorem K_sub (c d : Cert k) (m : ℕ) (β : Fin m) :
    Cert.K (c - d) m β = Cert.K c m β - Cert.K d m β :=
  map_sub ..

@[simp] theorem E_sub (c d : Cert k) (m : ℕ) (β : Fin m) :
    Cert.E (c - d) m β = Cert.E c m β - Cert.E d m β :=
  map_sub ..

@[simp] theorem K_neg (c : Cert k) (m : ℕ) (β : Fin m) : Cert.K (-c) m β = -Cert.K c m β :=
  map_neg ..

@[simp] theorem E_neg (c : Cert k) (m : ℕ) (β : Fin m) : Cert.E (-c) m β = -Cert.E c m β :=
  map_neg ..

@[simp] theorem K_zsmul (z : ℤ) (c : Cert k) (m : ℕ) (β : Fin m) :
    Cert.K (z • c) m β = z • Cert.K c m β := map_zsmul ..

@[simp] theorem E_zsmul (z : ℤ) (c : Cert k) (m : ℕ) (β : Fin m) :
    Cert.E (z • c) m β = z • Cert.E c m β := map_zsmul ..

theorem K_sum {ι : Type*} (s : Finset ι) (c : ι → Cert k) (m : ℕ) (β : Fin m) :
    Cert.K (∑ i ∈ s, c i) m β = ∑ i ∈ s, Cert.K (c i) m β := map_sum ..

theorem E_sum {ι : Type*} (s : Finset ι) (c : ι → Cert k) (m : ℕ) (β : Fin m) :
    Cert.E (∑ i ∈ s, c i) m β = ∑ i ∈ s, Cert.E (c i) m β := map_sum ..

/-- Every component of the combination is smaller than `D`. -/
def Smaller (c : Cert k) (D : Diagram (k + 1)) : Prop := ∀ y ∈ c.support, MeasureLT y.D D

theorem smaller_single {x : Comp k} {z : ℤ} {D : Diagram (k + 1)} (h : MeasureLT x.D D) :
    Cert.Smaller (Finsupp.single x z) D := by
  intro y hy
  rw [Finsupp.mem_support_iff] at hy
  by_cases hyx : y = x
  · exact hyx ▸ h
  · exact (hy (Finsupp.single_eq_of_ne' (Ne.symm hyx))).elim

theorem smaller_add {c d : Cert k} {D : Diagram (k + 1)} (hc : c.Smaller D)
    (hd : d.Smaller D) : Cert.Smaller (c + d) D := by
  intro y hy
  rcases Finset.mem_union.mp (Finsupp.support_add hy) with h | h
  · exact hc y h
  · exact hd y h

theorem smaller_neg {c : Cert k} {D : Diagram (k + 1)} (hc : c.Smaller D) :
    Cert.Smaller (-c) D := by
  intro y hy
  rw [Finsupp.support_neg] at hy
  exact hc y hy

theorem smaller_sub {c d : Cert k} {D : Diagram (k + 1)} (hc : c.Smaller D)
    (hd : d.Smaller D) : Cert.Smaller (c - d) D := by
  rw [sub_eq_add_neg]
  exact smaller_add hc (smaller_neg hd)

theorem smaller_zsmul {c : Cert k} {D : Diagram (k + 1)} (z : ℤ) (hc : c.Smaller D) :
    Cert.Smaller (z • c) D := fun y hy => hc y (Finsupp.support_smul hy)

theorem smaller_sum {ι : Type*} {s : Finset ι} {c : ι → Cert k} {D : Diagram (k + 1)}
    (hc : ∀ i ∈ s, Cert.Smaller (c i) D) :
    Cert.Smaller (∑ i ∈ s, c i) D := by
  intro y hy
  obtain ⟨i, hi, hy'⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hy)
  exact hc i hi y hy'

end Cert

/-- `c` certifies the right-marked values of the component `x` by smaller components. -/
def Certifies {k : ℕ} (x : Comp k) (c : Cert k) : Prop :=
  (∀ m β, x.K m β = Cert.K c m β ∧ x.E m β = Cert.E c m β) ∧
    Cert.Smaller c x.D

/-! ### Representatives of the components in a flip-closed set -/

section Representatives

variable {n : ℕ} {D : Diagram n}

/-- A chosen element of a nonempty finite set. -/
def repOf (K : Finset (Orientation D)) (hK : K.Nonempty) : Orientation D :=
  Classical.choose hK

theorem repOf_congr {K K' : Finset (Orientation D)} (h : K = K') (hK : K.Nonempty)
    (hK' : K'.Nonempty) : repOf K hK = repOf K' hK' := by
  subst h
  rfl

/-- A chosen state of the component of `θ`, depending only on that component. -/
def componentRep (θ : Orientation D) : Orientation D :=
  repOf (flipComponent D θ) ⟨θ, self_mem_flipComponent θ⟩

theorem componentRep_mem (θ : Orientation D) : componentRep θ ∈ flipComponent D θ :=
  Classical.choose_spec (⟨θ, self_mem_flipComponent θ⟩ : (flipComponent D θ).Nonempty)

theorem flipComponent_componentRep (θ : Orientation D) :
    flipComponent D (componentRep θ) = flipComponent D θ :=
  flipComponent_eq_of_mem (componentRep_mem θ)

theorem componentRep_eq_of_flipComponent_eq {θ η : Orientation D}
    (h : flipComponent D θ = flipComponent D η) : componentRep θ = componentRep η :=
  repOf_congr h _ _

/-- A flip-closed set is the disjoint union of the components of its representatives. -/
theorem exists_component_reps (S : Finset (Orientation D))
    (hS : ∀ θ ∈ S, flipComponent D θ ⊆ S) :
    ∃ R ⊆ S, (R : Set (Orientation D)).PairwiseDisjoint (flipComponent D) ∧
      S = R.biUnion (flipComponent D) := by
  refine ⟨S.image componentRep, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hr
    exact hS θ hθ (componentRep_mem θ)
  · intro r hr r' hr' hne
    obtain ⟨θ, -, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨θ', -, rfl⟩ := Finset.mem_image.mp hr'
    rw [Function.onFun, Finset.disjoint_left]
    intro η hη hη'
    apply hne
    apply componentRep_eq_of_flipComponent_eq
    calc flipComponent D θ = flipComponent D (componentRep θ) :=
          (flipComponent_componentRep θ).symm
      _ = flipComponent D η := (flipComponent_eq_of_mem hη).symm
      _ = flipComponent D (componentRep θ') := flipComponent_eq_of_mem hη'
      _ = flipComponent D θ' := flipComponent_componentRep θ'
  · ext η
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · intro hη
      exact ⟨componentRep η, ⟨η, hη, rfl⟩, by
        rw [flipComponent_componentRep]
        exact self_mem_flipComponent η⟩
    · rintro ⟨r, ⟨θ, hθ, rfl⟩, hη⟩
      rw [flipComponent_componentRep] at hη
      exact hS θ hθ hη

/-- Sums over a flip-closed set are sums of whole-component sums of representatives. -/
theorem sum_eq_sum_component_reps {M : Type*} [AddCommMonoid M] {S R : Finset (Orientation D)}
    (hR : (R : Set (Orientation D)).PairwiseDisjoint (flipComponent D))
    (hSR : S = R.biUnion (flipComponent D)) (f : Orientation D → M) :
    ∑ θ ∈ S, f θ = ∑ r ∈ R, ∑ η ∈ flipComponent D r, f η := by
  rw [hSR, Finset.sum_biUnion hR]

end Representatives

/-! ### The combination of all components in a flip-closed set -/

section Layers

variable {k : ℕ} {D : Diagram (k + 1)}

/-- The combination with coefficient one at each representative. -/
def repCert (hD : Forward D) (R : Finset (Orientation D)) : Cert k :=
  ∑ r ∈ R, Finsupp.single ⟨D, hD, r⟩ 1

theorem repCert_K (hD : Forward D) (R : Finset (Orientation D)) (m : ℕ) (β : Fin m) :
    Cert.K (repCert hD R) m β = ∑ r ∈ R, componentMarkedK r (Fin.last k) m β := by
  simp only [repCert, Cert.K_sum, Cert.K_single, one_smul, Comp.K]

theorem repCert_E (hD : Forward D) (R : Finset (Orientation D)) (m : ℕ) (β : Fin m) :
    Cert.E (repCert hD R) m β = ∑ r ∈ R, componentMarkedE r (Fin.last k) m β := by
  simp only [repCert, Cert.E_sum, Cert.E_single, one_smul, Comp.E]

theorem repCert_smaller (hD : Forward D) (R : Finset (Orientation D)) {E : Diagram (k + 1)}
    (h : MeasureLT D E) : Cert.Smaller (repCert hD R) E :=
  Cert.smaller_sum fun _ _ => Cert.smaller_single h

/-- A flip-closed set of states has a combination of whole components with its
marked values. -/
theorem exists_layerCert (hD : Forward D) (S : Finset (Orientation D))
    (hS : ∀ θ ∈ S, flipComponent D θ ⊆ S) :
    ∃ c : Cert k, (∀ m β, ∑ θ ∈ S, markedK θ (Fin.last k) m β = Cert.K c m β ∧
      ∑ θ ∈ S, markedE θ (Fin.last k) m β = Cert.E c m β) ∧
      ∀ {E : Diagram (k + 1)}, MeasureLT D E → Cert.Smaller c E := by
  obtain ⟨R, -, hR, hSR⟩ := exists_component_reps S hS
  refine ⟨repCert hD R, fun m β => ⟨?_, ?_⟩, fun h => repCert_smaller hD R h⟩
  · rw [repCert_K, sum_eq_sum_component_reps hR hSR]
    rfl
  · rw [repCert_E, sum_eq_sum_component_reps hR hSR]
    rfl

/-- A chosen combination of whole components for a flip-closed set of states. -/
def layerCert (hD : Forward D) (S : Finset (Orientation D))
    (hS : ∀ θ ∈ S, flipComponent D θ ⊆ S) : Cert k :=
  Classical.choose (exists_layerCert hD S hS)

theorem layerCert_K (hD : Forward D) (S : Finset (Orientation D))
    (hS : ∀ θ ∈ S, flipComponent D θ ⊆ S) (m : ℕ) (β : Fin m) :
    ∑ θ ∈ S, markedK θ (Fin.last k) m β = Cert.K (layerCert hD S hS) m β :=
  ((Classical.choose_spec (exists_layerCert hD S hS)).1 m β).1

theorem layerCert_E (hD : Forward D) (S : Finset (Orientation D))
    (hS : ∀ θ ∈ S, flipComponent D θ ⊆ S) (m : ℕ) (β : Fin m) :
    ∑ θ ∈ S, markedE θ (Fin.last k) m β = Cert.E (layerCert hD S hS) m β :=
  ((Classical.choose_spec (exists_layerCert hD S hS)).1 m β).2

theorem layerCert_smaller (hD : Forward D) (S : Finset (Orientation D))
    (hS : ∀ θ ∈ S, flipComponent D θ ⊆ S) {E : Diagram (k + 1)} (h : MeasureLT D E) :
    Cert.Smaller (layerCert hD S hS) E :=
  (Classical.choose_spec (exists_layerCert hD S hS)).2 h

end Layers

/-! ### Unmarked values of combinations -/

namespace Cert

variable {k : ℕ}

/-- The unmarked strict-coloring value of a combination. -/
def KU (c : Cert k) (m : ℕ) : XPoly m :=
  Finsupp.linearCombination ℤ (fun x : Comp k => componentStrictEnumerator x.D x.θ m) c

/-- The unmarked HRV value of a combination. -/
def EU (c : Cert k) (m : ℕ) : XPoly m :=
  Finsupp.linearCombination ℤ (fun x : Comp k => evalElementary m (componentHRV x.D x.θ)) c

theorem KU_eq_sum (c : Cert k) (m : ℕ) : Cert.KU c m = ∑ β : Fin m, Cert.K c m β := by
  unfold KU K
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  exact (sum_componentMarkedK x.θ (Fin.last k) m).symm

theorem EU_eq_sum (c : Cert k) (m : ℕ) : Cert.EU c m = ∑ β : Fin m, Cert.E c m β := by
  unfold EU E
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  exact (sum_componentMarkedE x.θ (Fin.last k) m).symm

@[simp] theorem KU_single (x : Comp k) (z : ℤ) (m : ℕ) :
    Cert.KU (Finsupp.single x z) m = z • componentStrictEnumerator x.D x.θ m :=
  Finsupp.linearCombination_single ..

@[simp] theorem EU_single (x : Comp k) (z : ℤ) (m : ℕ) :
    Cert.EU (Finsupp.single x z) m = z • evalElementary m (componentHRV x.D x.θ) :=
  Finsupp.linearCombination_single ..

theorem KU_sum {ι : Type*} (s : Finset ι) (c : ι → Cert k) (m : ℕ) :
    Cert.KU (∑ i ∈ s, c i) m = ∑ i ∈ s, Cert.KU (c i) m := map_sum ..

theorem EU_sum {ι : Type*} (s : Finset ι) (c : ι → Cert k) (m : ℕ) :
    Cert.EU (∑ i ∈ s, c i) m = ∑ i ∈ s, Cert.EU (c i) m := map_sum ..

end Cert

/-- `c` certifies the unmarked values of the component `x` by smaller components. -/
def UCertifies {k : ℕ} (x : Comp k) (c : Cert k) : Prop :=
  (∀ m, componentStrictEnumerator x.D x.θ m = Cert.KU c m ∧
    evalElementary m (componentHRV x.D x.θ) = Cert.EU c m) ∧ Cert.Smaller c x.D

theorem Certifies.uCertifies {k : ℕ} {x : Comp k} {c : Cert k} (h : Certifies x c) :
    UCertifies x c := by
  refine ⟨fun m => ⟨?_, ?_⟩, h.2⟩
  · rw [Cert.KU_eq_sum, ← sum_componentMarkedK x.θ (Fin.last k) m]
    exact Finset.sum_congr rfl fun β _ => (h.1 m β).1
  · rw [Cert.EU_eq_sum, ← sum_componentMarkedE x.θ (Fin.last k) m]
    exact Finset.sum_congr rfl fun β _ => (h.1 m β).2

end

end VerticalStripLLT.Circular.DiagramProof
