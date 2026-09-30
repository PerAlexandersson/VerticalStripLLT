import VerticalStripLLT.Components.DiagramProof.FiniteCoverPaths

/-! Replacing `it` by `ij` for two children `i < j` preserves unique outgoing covers. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {n : ℕ} {R S : Fin n → Fin n → Prop}

/-- Join one child below another, retaining the property of at most one outgoing cover. -/
theorem relationCover_rightUnique_after_child_merge
    (hforward : ∀ ⦃u v⦄, R u v → u < v)
    (hunique : Relator.RightUnique (RelationCover R))
    {i j t : Fin n} (hij : i < j) (hit : RelationCover R i t)
    (hjt : RelationCover R j t)
    (hswap : ∀ u v, S u v ↔ (u = i ∧ v = j) ∨ (R u v ∧ ¬ (u = i ∧ v = t))) :
    Relator.RightUnique (RelationCover S) := by
  let T : Fin n → Fin n → Prop := fun u v =>
    (u = i ∧ v = j) ∨ (RelationCover R u v ∧ ¬ (u = i ∧ v = t))
  have hTforward : ∀ ⦃u v⦄, T u v → u < v := by
    rintro u v (⟨rfl, rfl⟩ | ⟨h, _⟩)
    · exact hij
    · exact h.1
  have hTunique : Relator.RightUnique T := by
    intro u v w hv hw
    rcases hv with ⟨rfl, rfl⟩ | ⟨hv, hnv⟩
    · rcases hw with ⟨_, rfl⟩ | ⟨hw, hnw⟩
      · rfl
      · exact (hnw ⟨rfl, hunique hw hit⟩).elim
    · rcases hw with ⟨rfl, rfl⟩ | ⟨hw, _⟩
      · exact (hnv ⟨rfl, hunique hv hit⟩).elim
      · exact hunique hv hw
  have hTij : T i j := Or.inl ⟨rfl, rfl⟩
  have hTjt : T j t := Or.inr ⟨hjt, fun h => hij.ne h.1.symm⟩
  have mapCover {u v : Fin n} (hc : RelationCover R u v) :
      Relation.ReflTransGen T u v := by
    by_cases heq : u = i ∧ v = t
    · obtain ⟨rfl, rfl⟩ := heq
      exact (Relation.ReflTransGen.single hTij).tail hTjt
    · exact Relation.ReflTransGen.single (Or.inr ⟨hc, heq⟩)
  have mapR {u v : Fin n} (hp : Relation.ReflTransGen R u v) :
      Relation.ReflTransGen T u v := by
    have hc := relationCover_reachable hforward hp
    clear hp
    induction hc with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.trans (mapCover hs)
  have mapS {u v : Fin n} (hp : Relation.ReflTransGen S u v) :
      Relation.ReflTransGen T u v := by
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih =>
      rcases (hswap _ _).mp hs with ⟨rfl, rfl⟩ | ⟨hs, _⟩
      · exact ih.tail hTij
      · exact ih.trans (mapR (Relation.ReflTransGen.single hs))
  have mapT {u v : Fin n} (hp : Relation.ReflTransGen T u v) :
      Relation.ReflTransGen S u v := by
    apply Relation.ReflTransGen.mono ?_ _ _ hp
    intro a b hab
    apply (hswap a b).mpr
    exact hab.elim Or.inl (fun h => Or.inr ⟨rel_of_relationCover hforward h.1, h.2⟩)
  have mapSCover {u v : Fin n} (hc : RelationCover S u v) : RelationCover T u v := by
    refine ⟨hc.1, mapS hc.2.1, ?_⟩
    intro w huw hwv hp
    exact hc.2.2 w huw hwv ⟨mapT hp.1, mapT hp.2⟩
  intro u v w huv huw
  exact relationCover_rightUnique_of_rightUnique hTforward hTunique
    (mapSCover huv) (mapSCover huw)

end VerticalStripLLT.Circular.DiagramProof
