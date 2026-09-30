import VerticalStripLLT.Components.DiagramProof.RelationPaths
import Mathlib.Order.Hom.Basic

/-! Restriction of forward paths and covers to an order-convex core. -/

namespace VerticalStripLLT.Circular.DiagramProof

variable {V W : Type*} [LinearOrder V] [LinearOrder W]
  {R : V → V → Prop} {S : W → W → Prop}

/-- Every vertex between two core vertices belongs to the core. -/
def ConvexImage (ι : V ↪o W) : Prop :=
  ∀ u v z, ι u ≤ z → z ≤ ι v → ∃ w, ι w = z

/-- A forward path with endpoints in a convex core restricts to an actual core path. -/
theorem reachable_iff_of_convexImage (ι : V ↪o W) (hconvex : ConvexImage ι)
    (hforward : ∀ ⦃u v⦄, S u v → u < v)
    (hrel : ∀ u v, R u v ↔ S (ι u) (ι v)) (u v : V) :
    Relation.ReflTransGen S (ι u) (ι v) ↔ Relation.ReflTransGen R u v := by
  constructor
  · intro h
    have restrict {x : W} (hp : Relation.ReflTransGen S x (ι v)) :
        ∀ w, x = ι w → Relation.ReflTransGen R w v := by
      induction hp using Relation.ReflTransGen.head_induction_on with
      | refl =>
        intro w hw
        have hweq : w = v := ι.injective hw.symm
        subst w
        exact Relation.ReflTransGen.refl
      | @head x y hxy hyv ih =>
        intro w hw
        obtain ⟨z, hz⟩ := hconvex w v y (hw ▸ (hforward hxy).le)
          (reachable_le hforward hyv)
        apply (ih z hz.symm).head
        apply (hrel w z).mpr
        simpa only [← hw, hz] using hxy
    exact restrict h u rfl
  · intro h
    exact h.lift ι (fun u v hs => (hrel u v).mp hs)

/-- Convex restriction preserves the full cover test, including every intermediate vertex. -/
theorem relationCover_iff_of_convexImage (ι : V ↪o W) (hconvex : ConvexImage ι)
    (hforward : ∀ ⦃u v⦄, S u v → u < v)
    (hrel : ∀ u v, R u v ↔ S (ι u) (ι v)) (u v : V) :
    RelationCover S (ι u) (ι v) ↔ RelationCover R u v := by
  have paths := reachable_iff_of_convexImage ι hconvex hforward hrel
  constructor
  · rintro ⟨hlt, hreach, hcover⟩
    refine ⟨ι.lt_iff_lt.mp hlt, (paths u v).mp hreach, ?_⟩
    intro w huw hwv hw
    exact hcover (ι w) (ι.strictMono huw) (ι.strictMono hwv)
      ⟨(paths u w).mpr hw.1, (paths w v).mpr hw.2⟩
  · rintro ⟨hlt, hreach, hcover⟩
    refine ⟨ι.strictMono hlt, (paths u v).mpr hreach, ?_⟩
    intro z huz hzv hz
    obtain ⟨w, rfl⟩ := hconvex u v z huz.le hzv.le
    exact hcover w (ι.lt_iff_lt.mp huz) (ι.lt_iff_lt.mp hzv)
      ⟨(paths u w).mp hz.1, (paths w v).mp hz.2⟩

end VerticalStripLLT.Circular.DiagramProof
