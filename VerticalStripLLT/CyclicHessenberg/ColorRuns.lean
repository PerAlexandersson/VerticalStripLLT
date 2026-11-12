import Mathlib.Data.List.SplitBy
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Pairwise

set_option autoImplicit false

/-! Constant runs and their order in a monotone list. -/

namespace List

variable {α : Type*} [LinearOrder α]

/-- Split a list at each pair of unequal adjacent entries. -/
def equalityRuns (l : List α) : List (List α) :=
  l.splitBy fun a b => decide (a = b)

/-- Extract the head of every nonempty equality run. -/
def equalityRunHeads (l : List α) : List α :=
  (equalityRuns l).pmap (fun run hne => run.head hne)
    (fun run hmem => List.ne_nil_of_mem_splitBy hmem)

theorem mem_equalityRun_ne_nil {l run : List α} (h : run ∈ equalityRuns l) :
    run ≠ [] :=
  List.ne_nil_of_mem_splitBy h

/-- Each equality run consists of repetitions of its first entry. -/
theorem equalityRun_eq_replicate_head {l run : List α}
    (h : run ∈ equalityRuns l) :
    run = List.replicate run.length (run.head (mem_equalityRun_ne_nil h)) := by
  have hchainBool := List.isChain_of_mem_splitBy h
  have hchain : run.IsChain (· = ·) := by
    apply hchainBool.imp
    intro a b hab
    simpa using hab
  cases run with
  | nil => exact (mem_equalityRun_ne_nil h rfl).elim
  | cons a tail =>
      have hrep : tail = List.replicate tail.length a :=
        List.isChain_cons_eq_iff_eq_replicate.mp hchain
      change a :: tail = List.replicate (tail.length + 1) a
      rw [List.replicate_succ]
      exact congrArg (List.cons a) hrep

private def runCross (u v : List α) : Prop :=
  ∀ x ∈ u.getLast?, ∀ y ∈ v.head?, x ≤ y

private def runSeparated (u v : List α) : Prop :=
  ∃ hu hv, decide (u.getLast hu = v.head hv) = false

private def headsOfRuns (runs : List (List α)) (hne : ∀ r ∈ runs, r ≠ []) : List α :=
  runs.pmap (fun run h => run.head h) hne

private theorem headsOfRuns_isChain {runs : List (List α)}
    (hne : ∀ r ∈ runs, r ≠ [])
    (hconst : ∀ r (hr : r ∈ runs),
      r = List.replicate r.length (r.head (hne r hr)))
    (hcross : runs.IsChain runCross)
    (hsep : runs.IsChain runSeparated) :
    (headsOfRuns runs hne).IsChain (· < ·) := by
  induction runs with
  | nil => exact List.isChain_nil
  | cons a tail ih =>
      cases tail with
      | nil =>
          simpa [headsOfRuns] using
            (List.isChain_singleton (a.head (hne a (by simp))))
      | cons b tail =>
          have hneA := hne a (by simp)
          have hneB := hne b (by simp)
          have hconstA := hconst a (by simp)
          have hconstB := hconst b (by simp)
          have hcrossAB := (List.isChain_cons_cons.mp hcross).1
          have hsepAB := (List.isChain_cons_cons.mp hsep).1
          rcases hsepAB with ⟨ha, hb, hneq⟩
          have hlast : a.getLast ha = a.head hneA := by
            have hentries : ∀ x ∈ a, x = a.head hneA := by
              intro x hx
              have hm : x ∈ List.replicate a.length (a.head hneA) := hconstA ▸ hx
              exact (List.mem_replicate.mp hm).2
            exact hentries _ (List.getLast_mem ha)
          have hle : a.head hneA ≤ b.head hneB := by
            have h := hcrossAB (a.getLast ha) (List.getLast_mem_getLast? ha)
              (b.head hb) (List.head_mem_head? hb)
            exact hlast ▸ h
          have hneHead : a.head hneA ≠ b.head hneB := by
            intro heq
            apply of_decide_eq_false hneq
            exact hlast.trans heq
          have hlt : a.head hneA < b.head hneB := lt_of_le_of_ne hle hneHead
          have hneTail : ∀ r ∈ b :: tail, r ≠ [] := by
            intro r hr
            exact hne r (List.mem_cons_of_mem a hr)
          have hconstTail : ∀ r (hr : r ∈ b :: tail),
              r = List.replicate r.length (r.head (hneTail r hr)) := by
            intro r hr
            exact hconst r (List.mem_cons_of_mem a hr)
          have hcrossTail := (List.isChain_cons_cons.mp hcross).2
          have hsepTail := (List.isChain_cons_cons.mp hsep).2
          have htail := ih hneTail hconstTail hcrossTail hsepTail
          change (a.head hneA :: headsOfRuns (b :: tail) hneTail).IsChain (· < ·)
          exact List.isChain_cons_cons.mpr ⟨hlt, htail⟩

/-- The extracted heads of a nondecreasing list are strictly increasing. -/
theorem equalityRunHeads_pairwise_lt {l : List α} (hl : l.Pairwise (· ≤ ·)) :
    (equalityRunHeads l).Pairwise (· < ·) := by
  let runs := equalityRuns l
  have hnil : [] ∉ runs := by
    simp [runs, equalityRuns]
  have hchain : l.IsChain (· ≤ ·) := List.isChain_iff_pairwise.mpr hl
  have hflat : runs.flatten.IsChain (· ≤ ·) := by
    simpa [runs, equalityRuns] using hchain
  have hparts := (List.isChain_flatten hnil).mp hflat
  have hconst : ∀ r (hr : r ∈ runs),
      r = List.replicate r.length
        (r.head (mem_equalityRun_ne_nil hr)) := by
    intro r hr
    exact equalityRun_eq_replicate_head hr
  have hsep : runs.IsChain runSeparated := by
    exact List.isChain_getLast_head_splitBy (fun a b => decide (a = b)) l
  have hheads := headsOfRuns_isChain
    (fun r hr => mem_equalityRun_ne_nil hr)
    (by
      intro r hr
      exact hconst r hr)
    hparts.2 hsep
  change (headsOfRuns runs
    (fun r hr => mem_equalityRun_ne_nil hr)).Pairwise (· < ·)
  exact List.isChain_iff_pairwise.mp hheads

end List
