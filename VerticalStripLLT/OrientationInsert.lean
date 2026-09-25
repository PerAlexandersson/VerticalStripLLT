import VerticalStripLLT.Orientation

namespace VerticalStripLLT

noncomputable def orientationInsertEquiv {n : ℕ} {P R : SchroderPath n}
    (a : Fin n × Fin n) (hnot : a ∉ P.normalEdges)
    (hN : R.normalEdges = insert a P.normalEdges) :
    Orientation R ≃ Bool × Orientation P := by
  classical
  let ea : {e // e ∈ R.normalEdges} :=
    ⟨a, by rw [hN]; simp [hnot]⟩
  exact
    { toFun := fun θ =>
        (θ ea, fun e => θ ⟨e, by rw [hN]; simp [e.property]⟩)
      invFun := fun z e =>
        if he : e.1 = a then z.1 else
          z.2 ⟨e.1, by
            have hem := e.property
            have hem' : e.1 ∈ insert a P.normalEdges := by
              simpa only [hN] using hem
            simpa [he] using hem'⟩
      left_inv := by
        intro θ
        funext e
        by_cases he : e.1 = a
        · have he' : e = ea := Subtype.ext he
          simp only [dite_eq_left he]
          exact congrArg θ he'.symm
        · simp [he]
      right_inv := by
        rintro ⟨b, θ⟩
        apply Prod.ext
        · simp [ea]
        · funext e
          have he : e.1 ≠ a := by
            intro hea
            apply hnot
            simpa [hea] using e.property
          simp [he] }

private theorem card_filter_subtype {α : Type} [DecidableEq α]
    (s : Finset α) (f : {x // x ∈ s} → Bool) :
    (Finset.univ.filter fun x => f x = true).card =
      (s.filter fun x => if hx : x ∈ s then f ⟨x, hx⟩ = true
        else False).card := by
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_filter]
    exact ⟨x.2, by simp [x.2, hx]⟩
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro y hy
    simp only [Finset.mem_filter] at hy
    refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp [hy.1] at hy ⊢
    exact hy

theorem orientationAsc_insert {n : ℕ} {P R : SchroderPath n}
    (a : Fin n × Fin n) (hnot : a ∉ P.normalEdges)
    (hN : R.normalEdges = insert a P.normalEdges)
    (b : Bool) (θ : Orientation P) :
    orientationAsc R ((orientationInsertEquiv a hnot hN).symm (b, θ)) =
      orientationAsc P θ + if b then 1 else 0 := by
  classical
  let E := orientationInsertEquiv a hnot hN
  let ea : {e // e ∈ R.normalEdges} :=
    ⟨a, by rw [hN]; simp [hnot]⟩
  let θR : Orientation R := E.symm (b, θ)
  let fR : (Fin n × Fin n) → Bool := fun e =>
    if he : e ∈ R.normalEdges then θR ⟨e, he⟩ else false
  have hcardR : orientationAsc R θR =
      (R.normalEdges.filter fun e => fR e = true).card := by
    simpa [orientationAsc, fR] using
      (card_filter_subtype R.normalEdges
        (fun e : {x // x ∈ R.normalEdges} => θR e))
  have hcardP := card_filter_subtype P.normalEdges θ
  have hbase : ∀ e : {x // x ∈ P.normalEdges},
      fR e.1 = θ e := by
    intro e
    have he : e.1 ≠ a := by
      intro hea
      apply hnot
      simpa [hea] using e.property
    have heR : e.1 ∈ R.normalEdges := by
      rw [hN]
      exact Finset.mem_insert_of_mem e.property
    simp [fR, heR, he, θR, E, orientationInsertEquiv]
  have hfa : fR a = b := by
    simp [fR, hN, hnot, θR, E, orientationInsertEquiv]
  have hbaseCard :
      (P.normalEdges.filter fun e => fR e = true).card =
        orientationAsc P θ := by
    change _ = (Finset.univ.filter fun e => θ e = true).card
    rw [hcardP]
    congr 1
    ext e
    by_cases he : e ∈ P.normalEdges
    · simp [he, ← hbase ⟨e, he⟩]
    · simp [he]
  rw [hcardR, hN, Finset.filter_insert]
  cases b <;> simp [hfa, hnot, hbaseCard, Nat.add_comm]

end VerticalStripLLT
