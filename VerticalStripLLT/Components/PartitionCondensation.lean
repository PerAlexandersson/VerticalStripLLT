import VerticalStripLLT.Components.OrderedPartitionDAG
import Mathlib.Order.Antisymmetrization

/-!
# Condensation transport of actual compatible partitions

Block images and full block preimages give inverse maps on the finite
partition enumerators. Both maps preserve list length, hence the signed sum.
-/

namespace VerticalStripLLT.Components.OrderedPartitions

open scoped BigOperators Classical

noncomputable section

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Fintype V]

/-- A union of complete fibers of `q`. -/
def FiberSaturated (q : V → W) (S : Finset V) : Prop :=
  ∀ ⦃x y⦄, q x = q y → x ∈ S → y ∈ S

/-- Full finite preimage of a quotient block. -/
def blockPreimage (q : V → W) (B : Finset W) : Finset V :=
  Finset.univ.filter fun v => q v ∈ B

omit [DecidableEq V] in
@[simp]
theorem mem_blockPreimage (q : V → W) (B : Finset W) (v : V) :
    v ∈ blockPreimage q B ↔ q v ∈ B := by
  simp [blockPreimage]

omit [DecidableEq V] in
theorem blockPreimage_image (q : V → W) {S : Finset V} (hS : FiberSaturated q S) :
    blockPreimage q (S.image q) = S := by
  ext x
  simp only [mem_blockPreimage, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    exact hS heq hy
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [DecidableEq V] in
theorem image_blockPreimage (q : V → W) (hq : Function.Surjective q) (B : Finset W) :
    (blockPreimage q B).image q = B := by
  ext y
  simp only [Finset.mem_image, mem_blockPreimage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := hq y
    exact ⟨x, hy, rfl⟩

theorem blockPreimage_sdiff (q : V → W) (S B : Finset W) :
    blockPreimage q (S \ B) = blockPreimage q S \ blockPreimage q B := by
  ext x
  simp

omit [DecidableEq W] [Fintype V] in
theorem FiberSaturated.sdiff {q : V → W} {S U : Finset V}
    (hS : FiberSaturated q S) (hU : FiberSaturated q U) : FiberSaturated q (S \ U) := by
  intro x y hxy hx
  obtain ⟨hxS, hxU⟩ := Finset.mem_sdiff.mp hx
  exact Finset.mem_sdiff.mpr ⟨hS hxy hxS, fun hyU => hxU (hU hxy.symm hyU)⟩

omit [Fintype V] in
theorem image_sdiff_of_saturated (q : V → W) (S U : Finset V)
    (hU : FiberSaturated q U) : (S \ U).image q = S.image q \ U.image q := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxS, hxU⟩ := Finset.mem_sdiff.mp hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨x, hxS, rfl⟩, ?_⟩
    rintro hym
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hym
    exact hxU (hU hzx hz)
  · intro hy
    obtain ⟨hyS, hyU⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyS
    refine Finset.mem_image.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hx, ?_⟩, rfl⟩
    intro hxU
    exact hyU (Finset.mem_image.mpr ⟨x, hxU, rfl⟩)

section Pullback

variable (R : V → V → Prop) (T : W → W → Prop) (q : V → W)
  (hq : Function.Surjective q) (hrel : ∀ x y, R x y ↔ T (q x) (q y))

include hq hrel in
theorem compatible_blockPreimage {S : Finset W} {bs : List (Finset W)}
    (h : IsCompatible T S bs) :
    IsCompatible R (blockPreimage q S) (bs.map (blockPreimage q)) := by
  induction bs generalizing S with
  | nil =>
    change S = ∅ at h
    simp [h, IsCompatible, blockPreimage]
  | cons B bs ih =>
    obtain ⟨hB, hbs⟩ := h
    obtain ⟨hBS, hBne, hup⟩ := (mem_topBlocks T S B).mp hB
    change blockPreimage q B ∈ topBlocks R (blockPreimage q S) ∧ _
    constructor
    · apply (mem_topBlocks R _ _).mpr
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        exact (mem_blockPreimage q S x).mpr (hBS ((mem_blockPreimage q B x).mp hx))
      · obtain ⟨b, hb⟩ := hBne
        obtain ⟨x, rfl⟩ := hq b
        exact ⟨x, (mem_blockPreimage q B x).mpr hb⟩
      · intro x y hx hy hxy
        exact (mem_blockPreimage q B y).mpr
          (hup ((mem_blockPreimage q B x).mp hx)
            ((mem_blockPreimage q S y).mp hy) ((hrel x y).mp hxy))
    · simpa only [blockPreimage_sdiff] using ih hbs

include hrel in
private theorem compatible_image_and_inverse
    (hrefl : ∀ y, T y y) {S : Finset V} {bs : List (Finset V)}
    (hS : FiberSaturated q S) (h : IsCompatible R S bs) :
    IsCompatible T (S.image q) (bs.map (Finset.image q)) ∧
      (bs.map (Finset.image q)).map (blockPreimage q) = bs := by
  induction bs generalizing S with
  | nil =>
    change S = ∅ at h
    simp [h, IsCompatible]
  | cons U bs ih =>
    obtain ⟨hU, hbs⟩ := h
    obtain ⟨hUS, hUne, hup⟩ := (mem_topBlocks R S U).mp hU
    have hUsat : FiberSaturated q U := by
      intro x y heq hx
      apply hup hx (hS heq (hUS hx))
      apply (hrel x y).mpr
      rw [heq]
      exact hrefl (q y)
    obtain ⟨htail, hinv⟩ := ih (hS.sdiff hUsat) hbs
    constructor
    · change U.image q ∈ topBlocks T (S.image q) ∧ _
      constructor
      · apply (mem_topBlocks T _ _).mpr
        refine ⟨Finset.image_subset_image hUS, hUne.image q, ?_⟩
        intro x y hx hy hxy
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_image.mpr ⟨b, hup ha hb ((hrel a b).mpr hxy), rfl⟩
      · simpa only [image_sdiff_of_saturated q S U hUsat] using htail
    · simp only [List.map_cons, blockPreimage_image q hUsat, hinv]

include hrel in
/-- The quotient images are compatible, and pulling them back recovers every original block. -/
theorem compatible_blockImage
    (hrefl : ∀ y, T y y) {S : Finset V} {bs : List (Finset V)}
    (hS : FiberSaturated q S) (h : IsCompatible R S bs) :
    IsCompatible T (S.image q) (bs.map (Finset.image q)) :=
  (compatible_image_and_inverse R T q hrel hrefl hS h).1

include hq hrel in
/-- Transport of the existing finite signed sum, with no new enumerator. -/
theorem signedSum_image
    (hrefl : ∀ y, T y y) (S : Finset V) (hS : FiberSaturated q S) :
    signedSum R S = signedSum T (S.image q) := by
  unfold signedSum
  refine Finset.sum_bij'
    (fun bs _ => bs.map (Finset.image q))
    (fun bs _ => bs.map (blockPreimage q)) ?_ ?_ ?_ ?_ ?_
  · intro bs hbs
    apply (mem_partitions T _ _).mpr
    exact compatible_blockImage R T q hrel hrefl hS ((mem_partitions R _ _).mp hbs)
  · intro bs hbs
    apply (mem_partitions R _ _).mpr
    have h := compatible_blockPreimage R T q hq hrel ((mem_partitions T _ _).mp hbs)
    simpa only [blockPreimage_image q hS] using h
  · intro bs hbs
    exact (compatible_image_and_inverse R T q hrel hrefl hS
      ((mem_partitions R _ _).mp hbs)).2
  · intro bs hbs
    clear hbs
    induction bs with
    | nil => rfl
    | cons B bs ih => simp only [List.map_cons, image_blockPreimage q hq B, ih]
  · intro bs hbs
    simp only [List.length_map]

end Pullback

section Preorders

variable {A : Type*} [DecidableEq A]

theorem compatible_le_iff_lt [PartialOrder A] (S : Finset A) (bs : List (Finset A)) :
    IsCompatible (· ≤ ·) S bs ↔ IsCompatible (· < ·) S bs := by
  induction bs generalizing S with
  | nil => rfl
  | cons U bs ih =>
    have hup : UpClosed (· ≤ ·) S U ↔ UpClosed (· < ·) S U := by
      constructor
      · intro h x y hx hy hxy
        exact h hx hy hxy.le
      · intro h x y hx hy hxy
        rcases eq_or_lt_of_le hxy with rfl | hlt
        · exact hx
        · exact h hx hy hlt
    simp only [IsCompatible, mem_topBlocks, hup, ih]

theorem signedSum_le_eq_lt [PartialOrder A] (S : Finset A) :
    signedSum (· ≤ ·) S = signedSum (· < ·) S := by
  have heq : partitions (· ≤ ·) S = partitions (· < ·) S := by
    ext bs
    simp only [mem_partitions, compatible_le_iff_lt]
  simp only [signedSum, heq]

/-- A preorder's actual partition sum descends to its antisymmetrization. -/
theorem signedSum_antisymmetrization [Fintype A] [Preorder A] :
    signedSum (· ≤ ·) (Finset.univ : Finset A) =
      signedSum (fun x y : Antisymmetrization A (· ≤ ·) => x < y)
        (Finset.univ.image (toAntisymmetrization (α := A) (· ≤ ·))) := by
  classical
  rw [← signedSum_le_eq_lt]
  apply signedSum_image (· ≤ ·) (· ≤ ·) (toAntisymmetrization (α := A) (· ≤ ·))
  · intro x
    exact ⟨ofAntisymmetrization (· ≤ ·) x, by simp⟩
  · intro x y
    exact toAntisymmetrization_le_toAntisymmetrization_iff.symm
  · exact le_refl
  · intro x y hxy hx
    exact Finset.mem_univ y

end Preorders

/-- Downward closure ensures that a walk ending in `S` remains inside `S`. -/
def DownClosed (R : V → V → Prop) (S : Finset V) : Prop :=
  ∀ ⦃x y⦄, R x y → y ∈ S → x ∈ S

omit [DecidableEq V] [Fintype V] in
private theorem upClosed_reachability {R : V → V → Prop} {S U : Finset V}
    (hS : DownClosed R S) (hU : UpClosed R S U) :
    UpClosed (Relation.ReflTransGen R) S U := by
  intro x y hx hy hxy
  revert hy
  induction hxy with
  | refl => exact fun _ => hx
  | tail h hstep ih =>
    intro hy
    exact hU (ih (hS hstep hy)) hy hstep

omit [Fintype V] in
private theorem downClosed_sdiff {R : V → V → Prop} {S U : Finset V}
    (hS : DownClosed R S) (hU : UpClosed R S U) : DownClosed R (S \ U) := by
  intro x y hxy hy
  obtain ⟨hyS, hyU⟩ := Finset.mem_sdiff.mp hy
  exact Finset.mem_sdiff.mpr ⟨hS hxy hyS, fun hxU => hyU (hU hxU hyS hxy)⟩

omit [Fintype V] in
/-- Adding all reachable pairs does not change compatibility on a down-closed set. -/
theorem compatible_reachability_iff (R : V → V → Prop) (S : Finset V)
    (hS : DownClosed R S) (bs : List (Finset V)) :
    IsCompatible R S bs ↔ IsCompatible (Relation.ReflTransGen R) S bs := by
  induction bs generalizing S with
  | nil => rfl
  | cons U bs ih =>
    constructor
    · rintro ⟨hU, hbs⟩
      obtain ⟨hUS, hUne, hup⟩ := (mem_topBlocks R S U).mp hU
      refine ⟨(mem_topBlocks _ S U).mpr
        ⟨hUS, hUne, upClosed_reachability hS hup⟩, ?_⟩
      exact (ih (S \ U) (downClosed_sdiff hS hup)).mp hbs
    · rintro ⟨hU, hbs⟩
      obtain ⟨hUS, hUne, hup⟩ :=
        (mem_topBlocks (Relation.ReflTransGen R) S U).mp hU
      have hup' : UpClosed R S U := fun _ _ hx hy hxy =>
        hup hx hy (Relation.ReflTransGen.single hxy)
      refine ⟨(mem_topBlocks R S U).mpr ⟨hUS, hUne, hup'⟩, ?_⟩
      exact (ih (S \ U) (downClosed_sdiff hS hup')).mpr hbs

omit [Fintype V] in
theorem signedSum_reachability (R : V → V → Prop) (S : Finset V)
    (hS : DownClosed R S) :
    signedSum R S = signedSum (Relation.ReflTransGen R) S := by
  have heq : partitions R S = partitions (Relation.ReflTransGen R) S := by
    ext bs
    simp only [mem_partitions, compatible_reachability_iff R S hS]
  simp only [signedSum, heq]

/-- The reachability preorder used to form the strong-component quotient. -/
@[instance_reducible]
def reachabilityPreorder (R : V → V → Prop) : Preorder V where
  le := Relation.ReflTransGen R
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans

/-- The actual partition sum equals the sum on the strict reachability order
of strong components. The target relation is the transitive condensation. -/
theorem signedSum_condensation (R : V → V → Prop) :
    letI : Preorder V := reachabilityPreorder R
    signedSum R (Finset.univ : Finset V) =
      signedSum (fun x y : Antisymmetrization V (· ≤ ·) => x < y)
        (Finset.univ.image (toAntisymmetrization (α := V) (· ≤ ·))) := by
  let : Preorder V := reachabilityPreorder R
  calc
    signedSum R (Finset.univ : Finset V) =
        signedSum (Relation.ReflTransGen R) Finset.univ :=
      signedSum_reachability R Finset.univ (fun _ _ _ _ => Finset.mem_univ _)
    _ = _ := signedSum_antisymmetrization (A := V)

end

end VerticalStripLLT.Components.OrderedPartitions
