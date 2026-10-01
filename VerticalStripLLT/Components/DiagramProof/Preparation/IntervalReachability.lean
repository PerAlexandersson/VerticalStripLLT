import VerticalStripLLT.Components.DiagramProof.Preparation.IncomingNormalization
import VerticalStripLLT.Components.DiagramProof.Relations.UniqueIncomingPaths

/-! Once a weak path lies in its endpoint interval, incoming-fork normalization directs it. -/

namespace VerticalStripLLT.Circular.DiagramProof

section Relations

variable {V : Type*} [LinearOrder V] {R : V → V → Prop} {S : Set V}

/-- Forward paths between vertices of a convex set stay in its induced relation. -/
theorem reachable_within_iff_of_convex
    (hforward : ∀ ⦃x y⦄, R x y → x < y)
    (hconvex : ∀ x y z, S x → S y → x ≤ z → z ≤ y → S z)
    {u v : V} (hu : S u) (hv : S v) :
    Relation.ReflTransGen (fun x y => S x ∧ S y ∧ R x y) u v ↔
      Relation.ReflTransGen R u v := by
  constructor
  · exact Relation.ReflTransGen.mono (fun _ _ h => h.2.2) _ _
  · intro hp
    apply reachable_mono_on_interval hforward (lo := u) (hi := v) ?_ hp le_rfl le_rfl
    intro x y hux hyv hxy
    exact ⟨hconvex u v x hu hv hux ((hforward hxy).le.trans hyv),
      hconvex u v y hu hv (hux.trans (hforward hxy).le) hyv, hxy⟩

/-- Covers of an induced convex relation are exactly the ambient covers with both ends inside. -/
theorem relationCover_within_iff_of_convex
    (hforward : ∀ ⦃x y⦄, R x y → x < y)
    (hconvex : ∀ x y z, S x → S y → x ≤ z → z ≤ y → S z) (u v : V) :
    RelationCover (fun x y => S x ∧ S y ∧ R x y) u v ↔
      S u ∧ S v ∧ RelationCover R u v := by
  have paths {x y : V} (hx : S x) (hy : S y) :=
    reachable_within_iff_of_convex hforward hconvex hx hy
  constructor
  · intro hc
    obtain ⟨hu, hv, _⟩ := rel_of_relationCover (fun {_ _} h => hforward h.2.2) hc
    refine ⟨hu, hv, hc.1, (paths hu hv).mp hc.2.1, ?_⟩
    intro w huw hwv hw
    have hwS := hconvex u v w hu hv huw.le hwv.le
    exact hc.2.2 w huw hwv ⟨(paths hu hwS).mpr hw.1, (paths hwS hv).mpr hw.2⟩
  · rintro ⟨hu, hv, hc⟩
    refine ⟨hc.1, (paths hu hv).mpr hc.2.1, ?_⟩
    intro w huw hwv hw
    have hwS := hconvex u v w hu hv huw.le hwv.le
    exact hc.2.2 w huw hwv ⟨(paths hu hwS).mp hw.1, (paths hwS hv).mp hw.2⟩

end Relations

variable {n : ℕ} {D : Diagram n}

/-- Refining selected edges to covers preserves the weak blocks inside a convex set. -/
theorem weakReach_covers_within_iff (hforward : Forward D) (S : Set (Fin n))
    (hconvex : ∀ x y z, S x → S y → x ≤ z → z ≤ y → S z)
    (θ : Orientation D) (u v : Fin n) :
    Relation.EqvGen (fun x y => S x ∧ S y ∧ Cover θ x y) u v ↔
      Relation.EqvGen (fun x y => S x ∧ S y ∧ D.edgeData.selected θ.val x y) u v := by
  have hf : ∀ ⦃x y⦄, (S x ∧ S y ∧ D.edgeData.selected θ.val x y) → x < y :=
    fun {_ _} h => θ.selected_lt_of_forward hforward h.2.2
  have hc : RelationCover (fun x y => S x ∧ S y ∧ D.edgeData.selected θ.val x y) =
      (fun x y => S x ∧ S y ∧ Cover θ x y) := by
    funext x y
    exact propext (relationCover_within_iff_of_convex
      (fun {_ _} h => θ.selected_lt_of_forward hforward h) hconvex x y)
  simpa only [hc] using eqvGen_relationCover_iff hf u v

/-- A least vertex in a convex induced weak block can be made to reach that block.
The path changes only edges internal to the prescribed set. -/
theorem exists_reachable_within_of_minimal (hforward : Forward D)
    (S : Set (Fin n))
    (hconvex : ∀ x y z, S x → S y → x ≤ z → z ≤ y → S z)
    (θ : Orientation D) (u v : Fin n)
    (hmin : ∀ w,
      Relation.EqvGen (fun x y => S x ∧ S y ∧ D.edgeData.selected θ.val x y) u w → u ≤ w)
    (hweak : Relation.EqvGen
      (fun x y => S x ∧ S y ∧ D.edgeData.selected θ.val x y) u v) :
    ∃ η : Orientation D,
      Relation.ReflTransGen (fun α β => DirectedFlipWithin S β α) θ η ∧
        Relation.ReflTransGen (D.edgeData.selected η.val) u v := by
  obtain ⟨η, hp, hη⟩ := exists_leftUnique_covers_within hforward S θ
  have hblocks := weakReach_within_iff_of_reverse_directed_reachable (Set.Subset.refl S) hp
  let R := fun x y => S x ∧ S y ∧ D.edgeData.selected η.val x y
  have hRf : ∀ ⦃x y⦄, R x y → x < y :=
    fun {_ _} h => η.selected_lt_of_forward hforward h.2.2
  have hcovers := relationCover_within_iff_of_convex
    (fun {_ _} hs => η.selected_lt_of_forward hforward hs) hconvex
  have hunique : Relator.LeftUnique (RelationCover R) := by
    intro a b c hac hbc
    exact hη ((hcovers a c).mp hac) ((hcovers b c).mp hbc)
  have huv : Relation.ReflTransGen R u v :=
    reachable_of_eqvGen_of_minimal_of_leftUnique_relationCover hRf
      (fun w hw => hmin w ((hblocks u w).mpr hw)) ((hblocks u v).mp hweak) hunique
  exact ⟨η, hp, Relation.ReflTransGen.mono (fun _ _ h => h.2.2) _ _ huv⟩

/-- In particular, an induced weak path inside `[u,v]` can be made into a directed path. -/
theorem exists_reachable_within_interval (hforward : Forward D) (θ : Orientation D)
    (u v : Fin n) (huv : u ≤ v)
    (hweak : Relation.EqvGen
      (fun x y => (u ≤ x ∧ x ≤ v) ∧ (u ≤ y ∧ y ≤ v) ∧
        D.edgeData.selected θ.val x y) u v) :
    ∃ η : Orientation D,
      Relation.ReflTransGen
        (fun α β => DirectedFlipWithin {x | u ≤ x ∧ x ≤ v} β α) θ η ∧
        Relation.ReflTransGen (D.edgeData.selected η.val) u v := by
  let S : Set (Fin n) := {x | u ≤ x ∧ x ≤ v}
  have hmem {x y : Fin n}
      (h : Relation.EqvGen (fun a b => S a ∧ S b ∧ D.edgeData.selected θ.val a b) x y) :
      S x ↔ S y := by
    induction h with
    | rel a b hab => exact ⟨fun _ => hab.2.1, fun _ => hab.1⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  apply exists_reachable_within_of_minimal hforward S ?_ θ u v ?_ hweak
  · intro x y z hx hy hxz hzy
    exact ⟨hx.1.trans hxz, hzy.trans hy.2⟩
  · intro w hw
    exact ((hmem hw).mp ⟨le_rfl, huv⟩).1

end VerticalStripLLT.Circular.DiagramProof
