import VerticalStripLLT.Components.DiagramProof.Complete.Diagram
import VerticalStripLLT.Components.DiagramProof.Foundation.SelectedRelation
import VerticalStripLLT.Components.DiagramProof.Restriction.CoreExtension
import VerticalStripLLT.Components.DiagramProof.Foundation.WeakBlocks

/-! Restriction to a complete prefix and actual flip lifting with fixed exterior. -/

namespace VerticalStripLLT.Circular.DiagramProof

open Classical

noncomputable section

/-- Removing the greatest vertex from an actual complete-diagram state. -/
def completeRestrict {n : ℕ} (θ : Orientation (completeDiagram (n + 1))) :
    Orientation (completeDiagram n) :=
  ofSelectedRelation (complete_forward n)
    (fun u v => (completeDiagram (n + 1)).edgeData.selected θ.val u.castSucc v.castSucc)
    (by
      intro u v h
      apply (complete_naturalEdge_iff n u v).mpr
      exact θ.selected_lt_of_forward (complete_forward (n + 1)) h)
    (by simp)

@[simp]
theorem completeRestrict_selected {n : ℕ} (θ : Orientation (completeDiagram (n + 1)))
    (u v : Fin (n + 1)) :
    (completeDiagram n).edgeData.selected (completeRestrict θ).val u v ↔
      (completeDiagram (n + 1)).edgeData.selected θ.val u.castSucc v.castSucc :=
  selected_ofSelectedRelation ..

/-- Extend a prefix state while retaining exactly the old edges to the greatest vertex. -/
def completeExtend {n : ℕ} (θ : Orientation (completeDiagram (n + 1)))
    (α : Orientation (completeDiagram n)) : Orientation (completeDiagram (n + 1)) :=
  ofSelectedRelation (complete_forward (n + 1))
    (fun u v =>
      (∃ a b : Fin (n + 1), a.castSucc = u ∧ b.castSucc = v ∧
        (completeDiagram n).edgeData.selected α.val a b) ∨
      (v = Fin.last (n + 1) ∧ (completeDiagram (n + 1)).edgeData.selected θ.val u v))
    (by
      intro u v h
      apply (complete_naturalEdge_iff (n + 1) u v).mpr
      rcases h with ⟨a, b, rfl, rfl, hab⟩ | ⟨_, huv⟩
      · exact α.selected_lt_of_forward (complete_forward n) hab
      · exact θ.selected_lt_of_forward (complete_forward (n + 1)) huv)
    (by simp)

@[simp]
theorem completeExtend_selected {n : ℕ} (θ : Orientation (completeDiagram (n + 1)))
    (α : Orientation (completeDiagram n)) (u v : Fin (n + 2)) :
    (completeDiagram (n + 1)).edgeData.selected (completeExtend θ α).val u v ↔
      (∃ a b : Fin (n + 1), a.castSucc = u ∧ b.castSucc = v ∧
        (completeDiagram n).edgeData.selected α.val a b) ∨
      (v = Fin.last (n + 1) ∧ (completeDiagram (n + 1)).edgeData.selected θ.val u v) :=
  selected_ofSelectedRelation ..

@[simp]
theorem completeExtend_inside {n : ℕ} (θ : Orientation (completeDiagram (n + 1)))
    (α : Orientation (completeDiagram n)) (u v : Fin (n + 1)) :
    (completeDiagram (n + 1)).edgeData.selected
        (completeExtend θ α).val u.castSucc v.castSucc ↔
      (completeDiagram n).edgeData.selected α.val u v := by
  rw [completeExtend_selected]
  simp

@[simp]
theorem completeExtend_top {n : ℕ} (θ : Orientation (completeDiagram (n + 1)))
    (α : Orientation (completeDiagram n)) (u : Fin (n + 2)) :
    (completeDiagram (n + 1)).edgeData.selected
        (completeExtend θ α).val u (Fin.last (n + 1)) ↔
      (completeDiagram (n + 1)).edgeData.selected θ.val u (Fin.last (n + 1)) := by
  rw [completeExtend_selected]
  simp

/-- The prefix embedding is order-convex; a forward path cannot leave and return. -/
theorem convex_castSucc (n : ℕ) : ConvexImage (Fin.castSuccOrderEmb : Fin n ↪o Fin (n + 1)) := by
  intro u v z _ hzv
  have hz : z.val < n := lt_of_le_of_lt hzv v.isLt
  exact ⟨⟨z.val, hz⟩, rfl⟩

/-- The concrete prefix construction satisfies the existing flip-lifting interface. -/
def completeCoreExtension {n : ℕ} (θ : Orientation (completeDiagram (n + 1))) :
    CoreExtension (completeDiagram n) (completeDiagram (n + 1)) where
  embed := Fin.castSuccOrderEmb
  convex := convex_castSucc (n + 1)
  state := completeExtend θ
  inside := completeExtend_inside θ
  outside := by
    intro α β u v hout
    simp only [completeExtend_selected]
    have ha : ¬ ∃ a b : Fin (n + 1), a.castSucc = u ∧ b.castSucc = v ∧
        (completeDiagram n).edgeData.selected α.val a b := by
      rintro ⟨a, b, hu, hv, _⟩
      exact hout ⟨a, b, hu, hv⟩
    have hb : ¬ ∃ a b : Fin (n + 1), a.castSucc = u ∧ b.castSucc = v ∧
        (completeDiagram n).edgeData.selected β.val a b := by
      rintro ⟨a, b, hu, hv, _⟩
      exact hout ⟨a, b, hu, hv⟩
    simp only [ha, hb, false_or]

@[simp]
theorem completeExtend_restrict {n : ℕ} (θ : Orientation (completeDiagram (n + 1))) :
    completeExtend θ (completeRestrict θ) = θ := by
  apply fullSelection_injective
  ext e
  rw [mem_fullSelection_iff_selected, mem_fullSelection_iff_selected,
    completeExtend_selected]
  constructor
  · rintro (⟨a, b, ha, hb, hab⟩ | ⟨_, h⟩)
    · rw [completeRestrict_selected] at hab
      simpa only [ha, hb] using hab
    · exact h
  · intro he
    by_cases hh : e.head = Fin.last (n + 1)
    · exact Or.inr ⟨hh, he⟩
    · have hhead : e.head.val < n + 1 := by
        have h := e.head.isLt
        have hne : e.head.val ≠ n + 1 := fun h => hh (Fin.ext h)
        lia
      have htail : e.tail.val < n + 1 :=
        Nat.lt_trans (complete_forward (n + 1) e) hhead
      exact Or.inl ⟨⟨e.tail.val, htail⟩, ⟨e.head.val, hhead⟩, rfl, rfl,
        (completeRestrict_selected θ _ _).mpr he⟩

theorem completeRestrict_cover_iff {n : ℕ}
    (θ : Orientation (completeDiagram (n + 1))) (u v : Fin (n + 1)) :
    Cover (completeRestrict θ) u v ↔ Cover θ u.castSucc v.castSucc := by
  have h := (completeCoreExtension θ).cover_iff (complete_forward (n + 1))
    (completeRestrict θ) u v
  change Cover (completeExtend θ (completeRestrict θ)) u.castSucc v.castSucc ↔ _ at h
  rw [completeExtend_restrict] at h
  exact h.symm

theorem completeRestrict_reachable_iff {n : ℕ}
    (θ : Orientation (completeDiagram (n + 1))) (u v : Fin (n + 1)) :
    Relation.ReflTransGen ((completeDiagram n).edgeData.selected
        (completeRestrict θ).val) u v ↔
      Relation.ReflTransGen ((completeDiagram (n + 1)).edgeData.selected θ.val)
        u.castSucc v.castSucc := by
  exact (reachable_iff_of_convexImage Fin.castSuccOrderEmb (convex_castSucc (n + 1))
    (fun {_ _} h => θ.selected_lt_of_forward (complete_forward (n + 1)) h)
    (completeRestrict_selected θ) u v).symm

/-- Directed paths to the prefix top give connectivity of the actual restricted state. -/
theorem completeRestrict_connected {n : ℕ}
    (θ : Orientation (completeDiagram (n + 1)))
    (hp : ∀ v : Fin (n + 1),
      Relation.ReflTransGen ((completeDiagram (n + 1)).edgeData.selected θ.val)
        v.castSucc (Fin.last n).castSucc) : SelectedConnected (completeRestrict θ) := by
  have hpath (v : Fin (n + 1)) := (completeRestrict_reachable_iff θ v _).mpr (hp v)
  intro u v
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ (hpath u))
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ (hpath v)))

/-- Every actual prefix path lifts from the original state, fixing all top edges. -/
theorem complete_lift_reachable {n : ℕ} (θ : Orientation (completeDiagram (n + 1)))
    {α : Orientation (completeDiagram n)}
    (h : Relation.ReflTransGen (Flip (completeDiagram n)) (completeRestrict θ) α) :
    Relation.ReflTransGen (Flip (completeDiagram (n + 1))) θ (completeExtend θ α) := by
  have hp := (completeCoreExtension θ).lift_reachable
    (complete_forward (n + 1)) (complete_forward n) h
  change Relation.ReflTransGen _ (completeExtend θ (completeRestrict θ))
    (completeExtend θ α) at hp
  simpa only [completeExtend_restrict] using hp

end

end VerticalStripLLT.Circular.DiagramProof
