import VerticalStripLLT.PathInvariants

/-!
# The natural relation of an ordinary Schröder path

A column `u` of a path is left by an east or diagonal step from some height `y`.
The natural edges out of `u` (normal and strict together) are exactly the pairs
`u v` with `u < v ≤ top u`, where `top u` is `y` after a diagonal step and `y - 1`
after an east step. Since `top` is monotone, the natural relation is
interval-closed, and every strict edge is a maximal natural pair.
-/

namespace VerticalStripLLT

namespace Step

/-- The largest head of a natural edge leaving column `u`. -/
def topFrom (x y u : ℕ) : List Step → ℕ
  | [] => y
  | north :: w => topFrom x (y + 1) u w
  | diagonal :: w => if u = x then y else topFrom (x + 1) (y + 1) u w
  | east :: w => if u = x then y - 1 else topFrom (x + 1) y u w

/-- The heights only grow along a path, so a strict edge ends at or above the current
height. -/
theorem strictFrom_height_le (x y u v : ℕ) {w : List Step} :
    strictFrom x y u v w = true → y ≤ v := by
  intro h
  induction w generalizing x y with
  | nil => simp [strictFrom] at h
  | cons a w ih =>
    cases a <;> simp only [strictFrom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    · have := ih (x := x) (y := y + 1) h
      lia
    · rcases h with h | h
      · exact h.2.symm.le
      · have := ih (x := x + 1) (y := y + 1) h
        lia
    · exact ih (x := x + 1) (y := y) h

/-- Natural edges out of a visited column are the pairs below its top. -/
theorem natural_iff_topFrom (n x y u v : ℕ) {w : List Step}
    (hw : validFrom n x y w = true) (hxu : x ≤ u) (hun : u < n) :
    (normalFrom x y u v w = true ∨ strictFrom x y u v w = true) ↔
      u < v ∧ v ≤ topFrom x y u w := by
  induction w generalizing x y with
  | nil =>
    simp only [validFrom, Bool.and_eq_true, beq_iff_eq] at hw
    lia
  | cons a w ih =>
    cases a with
    | north =>
      simp only [validFrom] at hw
      simpa only [normalFrom, strictFrom, topFrom] using ih x (y + 1) hw hxu
    | diagonal =>
      simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hw
      simp only [normalFrom, strictFrom, topFrom, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq]
      by_cases hux : u = x
      · subst hux
        have hn : normalFrom (u + 1) (y + 1) u v w = false := by
          by_contra h
          have := normalFrom_lower_bound _ _ _ _ (Bool.not_eq_false _ ▸ h)
          lia
        have hs : strictFrom (u + 1) (y + 1) u v w = false := by
          by_contra h
          have := strictFrom_lower_bound _ _ _ _ (Bool.not_eq_false _ ▸ h)
          lia
        simp only [hn, hs, ite_true, true_and, Bool.false_eq_true, or_false]
        lia
      · simp only [hux, false_and, false_or, ite_false]
        exact ih (x + 1) (y + 1) hw.2 (by lia)
    | east =>
      simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hw
      simp only [normalFrom, strictFrom, topFrom, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq]
      by_cases hux : u = x
      · subst hux
        have hn : normalFrom (u + 1) y u v w = false := by
          by_contra h
          have := normalFrom_lower_bound _ _ _ _ (Bool.not_eq_false _ ▸ h)
          lia
        have hs : strictFrom (u + 1) y u v w = false := by
          by_contra h
          have := strictFrom_lower_bound _ _ _ _ (Bool.not_eq_false _ ▸ h)
          lia
        simp only [hn, hs, ite_true, true_and, Bool.false_eq_true, or_false]
        lia
      · simp only [hux, false_and, false_or, ite_false]
        exact ih (x + 1) y hw.2 (by lia)

/-- The top of a visited column is at least one below the current height. -/
theorem le_topFrom_add_one (n x y u : ℕ) {w : List Step}
    (hw : validFrom n x y w = true) (hxu : x ≤ u) (hun : u < n) :
    y ≤ topFrom x y u w + 1 := by
  induction w generalizing x y with
  | nil =>
    simp only [validFrom, Bool.and_eq_true, beq_iff_eq] at hw
    lia
  | cons a w ih =>
    cases a with
    | north =>
      simp only [validFrom] at hw
      have := ih x (y + 1) hw hxu
      simp only [topFrom]
      lia
    | diagonal =>
      simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hw
      simp only [topFrom]
      split_ifs with hux
      · lia
      · have := ih (x + 1) (y + 1) hw.2 (by lia)
        lia
    | east =>
      simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hw
      simp only [topFrom]
      split_ifs with hux
      · lia
      · exact ih (x + 1) y hw.2 (by lia)

/-- The top is monotone in the column. -/
theorem topFrom_mono (n x y u v : ℕ) {w : List Step}
    (hw : validFrom n x y w = true) (hxu : x ≤ u) (huv : u ≤ v) (hvn : v < n) :
    topFrom x y u w ≤ topFrom x y v w := by
  induction w generalizing x y with
  | nil =>
    simp only [validFrom, Bool.and_eq_true, beq_iff_eq] at hw
    lia
  | cons a w ih =>
    cases a with
    | north =>
      simp only [validFrom] at hw
      exact ih x (y + 1) hw hxu
    | diagonal =>
      simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hw
      simp only [topFrom]
      by_cases hux : u = x
      · by_cases hvx : v = x
        · simp [hux, hvx]
        · have := le_topFrom_add_one n (x + 1) (y + 1) v hw.2 (by lia) hvn
          simp only [hux, ite_true, hvx, ite_false]
          lia
      · have hvx : v ≠ x := by lia
        simp only [hux, hvx, ite_false]
        exact ih (x + 1) (y + 1) hw.2 (by lia)
    | east =>
      simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hw
      simp only [topFrom]
      by_cases hux : u = x
      · by_cases hvx : v = x
        · simp [hux, hvx]
        · have := le_topFrom_add_one n (x + 1) y v hw.2 (by lia) hvn
          simp only [hux, ite_true, hvx, ite_false]
          lia
      · have hvx : v ≠ x := by lia
        simp only [hux, hvx, ite_false]
        exact ih (x + 1) y hw.2 (by lia)

/-- A strict edge ends at the top of its column. -/
theorem topFrom_of_strictFrom (n x y u v : ℕ) {w : List Step}
    (hw : validFrom n x y w = true) (h : strictFrom x y u v w = true) :
    topFrom x y u w = v := by
  induction w generalizing x y with
  | nil => simp [strictFrom] at h
  | cons a w ih =>
    cases a with
    | north =>
      simp only [validFrom] at hw
      simp only [strictFrom] at h
      exact ih x (y + 1) hw h
    | diagonal =>
      simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hw
      simp only [strictFrom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      simp only [topFrom]
      rcases h with ⟨rfl, rfl⟩ | h
      · simp
      · have := strictFrom_lower_bound _ _ _ _ h
        rw [ite_eq_right (show ¬ u = x by lia)]
        exact ih (x + 1) (y + 1) hw.2 h
    | east =>
      simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hw
      simp only [strictFrom] at h
      simp only [topFrom]
      have := strictFrom_lower_bound _ _ _ _ h
      rw [ite_eq_right (show ¬ u = x by lia)]
      exact ih (x + 1) y hw.2 h

/-- Every column before the tail of a strict edge has a lower top. -/
theorem topFrom_lt_of_strictFrom (n x y s t u : ℕ) {w : List Step}
    (hw : validFrom n x y w = true) (h : strictFrom x y s t w = true)
    (hxu : x ≤ u) (hus : u < s) : topFrom x y u w < t := by
  induction w generalizing x y with
  | nil => simp [strictFrom] at h
  | cons a w ih =>
    cases a with
    | north =>
      simp only [validFrom] at hw
      simp only [strictFrom] at h
      exact ih x (y + 1) hw h hxu
    | diagonal =>
      simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hw
      simp only [strictFrom, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      simp only [topFrom]
      rcases h with ⟨rfl, rfl⟩ | h
      · lia
      · split_ifs with hux
        · have := strictFrom_height_le _ _ _ _ h
          lia
        · exact ih (x + 1) (y + 1) hw.2 h (by lia)
    | east =>
      simp only [validFrom, Bool.and_eq_true, decide_eq_true_eq] at hw
      simp only [strictFrom] at h
      simp only [topFrom]
      split_ifs with hux
      · have := strictFrom_height_le _ _ _ _ h
        lia
      · exact ih (x + 1) y hw.2 h (by lia)

end Step

namespace SchroderPath

variable {n : ℕ} (P : SchroderPath n)

/-- The natural relation of a path: its normal and strict edges together. -/
def NaturalPair (u v : Fin n) : Prop :=
  (u, v) ∈ P.normalEdges ∨ (u, v) ∈ P.strictEdges

/-- The largest head of a natural edge leaving `u`. -/
def top (u : Fin n) : ℕ := Step.topFrom 0 0 u.val P.steps

theorem naturalPair_iff (u v : Fin n) : P.NaturalPair u v ↔ u < v ∧ v.val ≤ P.top u := by
  have h := Step.natural_iff_topFrom n 0 0 u.val v.val P.valid (Nat.zero_le _) u.isLt
  simp only [NaturalPair, normalEdges, strictEdges, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact h

theorem top_mono {u v : Fin n} (huv : u ≤ v) : P.top u ≤ P.top v :=
  Step.topFrom_mono n 0 0 u.val v.val P.valid (Nat.zero_le _) huv v.isLt

/-- The natural relation of a path is forward. -/
theorem naturalPair_forward {u v : Fin n} (h : P.NaturalPair u v) : u < v :=
  ((P.naturalPair_iff u v).mp h).1

/-- The natural relation of a path is interval-closed. -/
theorem naturalPair_interval {u v w : Fin n} (h : P.NaturalPair u w) (huv : u < v)
    (hvw : v < w) : P.NaturalPair u v ∧ P.NaturalPair v w := by
  have h' := (P.naturalPair_iff u w).mp h
  have hmono := P.top_mono huv.le
  refine ⟨(P.naturalPair_iff u v).mpr ⟨huv, ?_⟩, (P.naturalPair_iff v w).mpr ⟨hvw, ?_⟩⟩
  · have : v.val < w.val := hvw
    lia
  · lia

/-- Every strict edge of a path is a maximal natural pair. -/
theorem strict_maximal {s t : Fin n} (hst : (s, t) ∈ P.strictEdges) :
    P.NaturalPair s t ∧
      ∀ x y, P.NaturalPair x y → x ≤ s → t ≤ y → x = s ∧ y = t := by
  have hs : Step.strictFrom 0 0 s.val t.val P.steps = true := by
    simpa [strictEdges] using hst
  have htop : P.top s = t.val := Step.topFrom_of_strictFrom n 0 0 _ _ P.valid hs
  refine ⟨Or.inr hst, fun x y hxy hxs hty => ?_⟩
  have hxy' := (P.naturalPair_iff x y).mp hxy
  have hx : x = s := by
    by_contra hne
    have hlt : x.val < s.val := lt_of_le_of_ne hxs (fun h => hne (Fin.ext h))
    have := Step.topFrom_lt_of_strictFrom n 0 0 s.val t.val x.val P.valid hs
      (Nat.zero_le _) hlt
    have : t.val ≤ y.val := hty
    simp only [top] at hxy'
    lia
  subst hx
  refine ⟨rfl, Fin.ext ?_⟩
  have : t.val ≤ y.val := hty
  lia

end SchroderPath

end VerticalStripLLT
