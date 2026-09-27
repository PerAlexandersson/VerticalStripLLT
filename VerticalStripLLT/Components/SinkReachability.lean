import VerticalStripLLT.Components.BlockExtractor
import Mathlib.Logic.Relation

/-! Reachability and sinks in a finite forward relation. -/

namespace VerticalStripLLT.Components

noncomputable section

variable {V : Type*} [LinearOrder V]

/-- The relation obtained by restricting `R` to a finite vertex set. -/
def inducedStep (R : V → V → Prop) (B : Finset V) (u v : V) : Prop :=
  u ∈ B ∧ v ∈ B ∧ R u v

private theorem le_of_induced_reach (R : V → V → Prop)
    (hforward : ∀ ⦃u v⦄, R u v → u < v) {B : Finset V} {u v : V}
    (h : Relation.ReflTransGen (inducedStep R B) u v) : u ≤ v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    exact ih.trans (le_of_lt (hforward hstep.2.2))

/-- Every vertex in a finite forward relation reaches an induced sink. -/
theorem exists_induced_sink_reachable (R : V → V → Prop)
    (hforward : ∀ ⦃u v⦄, R u v → u < v) (B : Finset V) {u : V}
    (hu : u ∈ B) :
    ∃ v, sinkOn R B v ∧
      Relation.ReflTransGen (inducedStep R B) u v := by
  classical
  let reach : Finset V :=
    B.filter (fun v => Relation.ReflTransGen (inducedStep R B) u v)
  have hreach : reach.Nonempty := by
    refine ⟨u, ?_⟩
    exact Finset.mem_filter.mpr ⟨hu, Relation.ReflTransGen.refl⟩
  let r : V := reach.max' hreach
  have hrreach : r ∈ reach := by
    dsimp [r]
    exact Finset.max'_mem reach hreach
  have hrB : r ∈ B := (Finset.mem_filter.mp hrreach).1
  have hur : Relation.ReflTransGen (inducedStep R B) u r :=
    (Finset.mem_filter.mp hrreach).2
  refine ⟨r, ?_, hur⟩
  refine ⟨hrB, ?_⟩
  intro v hv hrv
  have huv : Relation.ReflTransGen (inducedStep R B) u v :=
    Relation.ReflTransGen.tail hur ⟨hrB, hv, hrv⟩
  have hvreach : v ∈ reach := Finset.mem_filter.mpr ⟨hv, huv⟩
  have hvr : v ≤ r := by
    dsimp [r]
    exact Finset.le_max' reach v hvreach
  exact (not_lt_of_ge hvr) (hforward hrv)

/-- All vertices reach `r` exactly when `r` is the unique induced sink. -/
theorem reaches_iff_unique_induced_sink (R : V → V → Prop)
    (hforward : ∀ ⦃u v⦄, R u v → u < v) (B : Finset V) {r : V}
    (hr : r ∈ B) :
    (∀ v ∈ B, sinkOn R B v ↔ v = r) ↔
      ∀ v ∈ B, Relation.ReflTransGen (inducedStep R B) v r := by
  constructor
  · intro h v hv
    obtain ⟨s, hsink, hvs⟩ := exists_induced_sink_reachable R hforward B hv
    have hsr : s = r := (h s hsink.1).mp hsink
    simpa [hsr] using hvs
  · intro hall v hv
    constructor
    · intro hsink
      rcases Relation.ReflTransGen.cases_head (hall v hv) with h | ⟨z, hstep, _⟩
      · exact h
      · exact False.elim ((hsink.2 z hstep.2.1) hstep.2.2)
    · intro hvr
      subst v
      refine ⟨hr, ?_⟩
      intro w hw hrw
      have hwr : Relation.ReflTransGen (inducedStep R B) w r := hall w hw
      have hle : w ≤ r := le_of_induced_reach R hforward hwr
      exact (not_lt_of_ge hle) (hforward hrw)

end

end VerticalStripLLT.Components
