import VerticalStripLLT.Components.BalancedComponentLifts
import VerticalStripLLT.Components.ShortEdges
import Mathlib.Data.Finset.Sort

/-! Sorting compatible lifts and the interval relation they induce. -/

namespace VerticalStripLLT.Circular.Diagram

open Classical

noncomputable section

variable {n : ℕ} (D : Diagram n)

/-- Any injective choice of integer lifts has a finite increasing enumeration. -/
theorem exists_increasing_liftOrder (q : Fin n → ℤ) (hinj : Function.Injective q) :
    ∃ σ : Fin n ≃ Fin n, StrictMono (q ∘ σ) := by
  let s := Finset.univ.image q
  have hs : s.card = n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
  let f : Fin n → s := fun v => ⟨q v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      exact hinj (congrArg Subtype.val h)
    · intro z
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp z.property
      exact ⟨v, Subtype.ext hv⟩
  let e := Equiv.ofBijective f hf
  let σ := (s.orderIsoOfFin hs).toEquiv.trans e.symm
  have hq (i : Fin n) : q (σ i) = s.orderEmbOfFin hs i := by
    have h := congrArg Subtype.val (e.apply_symm_apply (s.orderIsoOfFin hs i))
    exact h
  refine ⟨σ, ?_⟩
  intro i j hij
  change q (σ i) < q (σ j)
  rw [hq, hq]
  exact (s.orderEmbOfFin hs).strictMono hij

/-- The natural edges compatible with specified lifts, indexed in a specified order. -/
def compatibleLiftRelation (q : Fin n → ℤ) (σ : Fin n ≃ Fin n)
    (i j : Fin n) : Prop :=
  ∃ e : Edge D.area, D.naturalLift e (q (σ i)) (q (σ j))

theorem compatibleLiftRelation_forward {q : Fin n → ℤ} {σ : Fin n ≃ Fin n}
    (hmono : StrictMono (q ∘ σ)) {i j : Fin n}
    (h : D.compatibleLiftRelation q σ i j) : i < j := by
  obtain ⟨e, he⟩ := h
  have hlt : q (σ i) < q (σ j) := by
    have hpos : 0 < e.length.val := e.property.1
    have hlen := he.2
    lia
  exact hmono.lt_iff_lt.mp hlt

/-- Every intermediate chosen lift gives both natural short edges. -/
theorem compatibleLiftRelation_interval {q : Fin n → ℤ} {σ : Fin n ≃ Fin n}
    (hmono : StrictMono (q ∘ σ)) {i j k : Fin n}
    (h : D.compatibleLiftRelation q σ i k) (hij : i < j) (hjk : j < k) :
    D.compatibleLiftRelation q σ i j ∧ D.compatibleLiftRelation q σ j k := by
  obtain ⟨e, he⟩ := h
  obtain ⟨eij, ejk, _, _, hij', hjk'⟩ :=
    D.normalShortEdges_of_naturalLift he (hmono hij) (hmono hjk)
  exact ⟨⟨eij, hij'⟩, ⟨ejk, hjk'⟩⟩

/-- Compatibility records exactly the endpoints and the original physical length. -/
theorem naturalLift_chosen_iff {q : Fin n → ℤ}
    (hq : ∀ v, D.residue (q v) = v) (e : Edge D.area) (u v : Fin n) :
    D.naturalLift e (q u) (q v) ↔
      e.tail = u ∧ e.head = v ∧ q v - q u = (e.length.val : ℤ) := by
  constructor
  · intro h
    have ht : e.tail = u := h.1.symm.trans (hq u)
    have hh : e.head = v := by
      have hr := D.residue_add_length e (q u) h.1
      rw [← h.2, hq] at hr
      exact hr.symm
    exact ⟨ht, hh, by have := h.2; lia⟩
  · rintro ⟨ht, hh, hlen⟩
    exact ⟨(hq u).trans ht.symm, by lia⟩

/-- Every selected edge of a balanced orientation belongs to the compatible relation. -/
theorem selected_compatibleLiftRelation (θ : Orientation D) {q : Fin n → ℤ}
    (hq : ∀ v, D.residue (q v) = v)
    (hp : D.naturalGain.BalancedPotential (D.strict ∪ θ.val) q)
    (σ : Fin n ≃ Fin n) {u v : Fin n} (h : D.edgeData.selected θ.val u v) :
    D.compatibleLiftRelation q σ (σ.symm u) (σ.symm v) := by
  obtain ⟨e, he, ht, hh⟩ := h
  refine ⟨e, ?_⟩
  simp only [Equiv.apply_symm_apply]
  apply (D.naturalLift_chosen_iff hq e u v).mpr
  refine ⟨ht, hh, ?_⟩
  change e.tail = u at ht
  change e.head = v at hh
  have hlen := hp e he
  change q e.head - q e.tail = (e.length.val : ℤ) at hlen
  simpa only [ht, hh] using hlen

end

end VerticalStripLLT.Circular.Diagram
