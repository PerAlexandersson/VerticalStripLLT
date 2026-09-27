import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Multiset.UnionInter

/-! Cancellation of common edge occurrences in two signed lists. -/

namespace VerticalStripLLT.Components

open Classical

noncomputable section

variable {E : Type*} [DecidableEq E]

def residualPositive (P N : List E) : List E :=
  P.diff N

def residualNegative (P N : List E) : List E :=
  N.diff P

theorem mem_residualPositive {P N : List E} {e : E}
    (h : e ∈ residualPositive P N) : e ∈ P := by
  have hm : e ∈ (P : Multiset E) - (N : Multiset E) := by
    simpa [residualPositive] using h
  exact Multiset.mem_of_le (Multiset.sub_le_self _ _) hm

theorem mem_residualNegative {P N : List E} {e : E}
    (h : e ∈ residualNegative P N) : e ∈ N := by
  have hm : e ∈ (N : Multiset E) - (P : Multiset E) := by
    simpa [residualNegative] using h
  exact Multiset.mem_of_le (Multiset.sub_le_self _ _) hm

theorem residual_disjoint (P N : List E) :
    (residualPositive P N).Disjoint (residualNegative P N) := by
  have hdis : Disjoint ((P : Multiset E) - (N : Multiset E))
      ((N : Multiset E) - (P : Multiset E)) := by
    rw [Multiset.disjoint_left]
    intro e hep hen
    rw [Multiset.mem_sub] at hep hen
    lia
  simpa [residualPositive, residualNegative] using hdis

theorem residual_endpoint_perm
    {V : Type*} (tail head : E → V) {P N : List E}
    (hperm : (P.map head ++ N.map tail).Perm
      (P.map tail ++ N.map head)) :
    ((residualPositive P N).map head ++
          (residualNegative P N).map tail).Perm
      ((residualPositive P N).map tail ++
          (residualNegative P N).map head) := by
  let p : Multiset E := P
  let q : Multiset E := N
  let i : Multiset E := p ∩ q
  have hend : p.map head + q.map tail = p.map tail + q.map head := by
    simpa [p, q] using (Multiset.coe_eq_coe.mpr hperm)
  have hpc : p - q + i = p := by
    exact Multiset.sub_add_inter p q
  have hqc : q - p + i = q := by
    simpa only [i, Multiset.inter_comm] using Multiset.sub_add_inter q p
  have hpmap (f : E → V) : p.map f = (p - q).map f + i.map f := by
    rw [← Multiset.map_add, hpc]
  have hqmap (f : E → V) : q.map f = (q - p).map f + i.map f := by
    rw [← Multiset.map_add, hqc]
  rw [hpmap head, hpmap tail, hqmap head, hqmap tail] at hend
  have hcancel :
      (p - q).map head + (q - p).map tail +
          (i.map head + i.map tail) =
        (p - q).map tail + (q - p).map head +
          (i.map head + i.map tail) := by
    simpa [add_assoc, add_comm, add_left_comm] using hend
  have hres :
      (p - q).map head + (q - p).map tail =
        (p - q).map tail + (q - p).map head := by
    exact add_right_cancel hcancel
  apply Multiset.coe_eq_coe.mp
  simpa [residualPositive, residualNegative, p, q, i] using hres

theorem residual_gain_sub_eq
    (gain : E → ℤ) (P N : List E) :
    (P.map gain).sum - (N.map gain).sum =
      ((residualPositive P N).map gain).sum -
        ((residualNegative P N).map gain).sum := by
  let p : Multiset E := P
  let q : Multiset E := N
  let i : Multiset E := p ∩ q
  have hp := congrArg (fun s : Multiset E => (s.map gain).sum)
    (Multiset.sub_add_inter p q)
  have hq := congrArg (fun s : Multiset E => (s.map gain).sum)
    (Multiset.sub_add_inter q p)
  rw [Multiset.inter_comm q p] at hq
  simp only [Multiset.map_add, Multiset.sum_add] at hp hq
  have hdiff : (p.map gain).sum - (q.map gain).sum =
      ((p - q).map gain).sum - ((q - p).map gain).sum := by
    lia
  simpa [residualPositive, residualNegative, p, q, i] using hdiff

end

end VerticalStripLLT.Components
