import VerticalStripLLT.Circular.DNLocalData
import VerticalStripLLT.Circular.OrientationPairSum

set_option backward.isDefEq.respectTransparency false

-- NEW MODULE VerticalStripLLT.Circular.DNSwapGeometry

/-! The periodic swap of `i` and `y` acting on lifted natural edges of a DN
configuration, controlled by the boundary of the diagram with `e` deleted. -/

namespace VerticalStripLLT.Circular

open scoped BigOperators Classical

namespace Diagram

variable {n : ℕ} (D : Diagram n)

section DN

variable (e f : Edge D.area) (he : e ∈ D.strict) (hf : f ∈ D.strict)
  (hcontact : f.tail = e.head)
  (heq : D.area.area (D.area.next e.head) = D.area.area e.head)
  (hb : D.area.area e.head + 1 < n)
  (hns : ∀ g ∈ D.strict, g.head ≠ D.area.next e.head)
  (hlen : 2 ≤ f.length.val)
  (hgap : D.area.area (D.area.next f.head) < D.area.area f.head)

include he hb in
theorem dn_res_swap (z : ℤ) :
    D.residue (periodicSwap n (e.head.val : ℤ) z) =
      Equiv.swap e.head (D.area.next e.head) (D.residue z) := by
  have hn : 2 ≤ n := by have := D.dn_three_le e he hb; lia
  rw [D.residue_periodicSwap hn, dn_res_p, dn_res_p1]

include he hb in
theorem dn_ps_I {z : ℤ} (hz : D.residue z = e.head) :
    periodicSwap n (e.head.val : ℤ) z = z + 1 := by
  have hn := D.dn_two_le e he hb
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period (hz.trans (D.dn_res_p e).symm)
  subst hk
  rw [periodicSwap_translate _ _ _ _ hn]
  have := (periodicSwap_base n (e.head.val : ℤ) 0 hn).1
  simp only [mul_zero, add_zero] at this
  rw [this]
  ring

include he hb in
theorem dn_ps_Y {z : ℤ} (hz : D.residue z = D.area.next e.head) :
    periodicSwap n (e.head.val : ℤ) z = z - 1 := by
  have hn := D.dn_two_le e he hb
  obtain ⟨k, hk⟩ := D.residue_eq_exists_period (hz.trans (D.dn_res_p1 e).symm)
  subst hk
  rw [periodicSwap_translate _ _ _ _ hn]
  have := (periodicSwap_base n (e.head.val : ℤ) 0 hn).2
  simp only [mul_zero, add_zero] at this
  rw [this]
  ring

include he hb in
theorem dn_ps_fix {z : ℤ} (h1 : D.residue z ≠ e.head)
    (h2 : D.residue z ≠ D.area.next e.head) :
    periodicSwap n (e.head.val : ℤ) z = z := by
  have hn := D.dn_two_le e he hb
  unfold periodicSwap
  rw [ite_eq_right, ite_eq_right]
  · intro h
    apply h2
    rw [← D.dn_res_p1 e]
    apply (D.residue_eq_iff_mod_sub_zero).mpr
    have h1n : (1 : ℤ) % n = 1 := Int.emod_eq_of_lt (by lia) (by lia)
    rw [show z - ((e.head.val : ℤ) + 1) = (z - e.head.val) - 1 by ring, Int.sub_emod, h, h1n]
    simp
  · intro h
    exact h1 (((D.residue_eq_iff_mod_sub_zero).mpr h).trans (D.dn_res_p e))

include he hf hcontact heq hb hgap in
theorem dn_geo {ε : Edge D.area} (hεe : ε ≠ e) (hεg : ε ≠ D.dnG e he heq) {x y : ℤ}
    (h : D.naturalLift ε x y) :
    (D.deleteCorner e (D.strict_corner e he)).boundary (periodicSwap n (e.head.val : ℤ) y) ≤
        periodicSwap n (e.head.val : ℤ) x ∧
      periodicSwap n (e.head.val : ℤ) x < periodicSwap n (e.head.val : ℤ) y ∧
      ¬ periodicBridge n (e.head.val : ℤ) (periodicSwap n (e.head.val : ℤ) x)
        (periodicSwap n (e.head.val : ℤ) y) := by
  have hn := D.dn_two_le e he hb
  have hbR : (D.deleteCorner e (D.strict_corner e he)).boundary y ≤ x := by
    rw [D.dn_R_boundary e he]
    have hbd := (D.naturalLift_boundary h).1
    split_ifs with hy
    · have hhead : ε.head = e.head := (D.naturalLift_head h).trans hy
      have hlen_ne : ε.length.val ≠ e.length.val := by
        intro hl
        apply hεe
        apply Subtype.ext
        exact Prod.ext hhead (Fin.ext hl)
      have hle := ε.length_le_area
      rw [hhead, ← D.dn_Le e he] at hle
      have hx := h.2
      rw [boundary, hy, ← D.dn_Le e he]
      lia
    · lia
  have hnb : ¬ periodicBridge n (e.head.val : ℤ) x y := by
    rintro ⟨k, hx, hy⟩
    apply hεg
    apply D.edge_eq_of_endpoints
    · rw [dnG_tail, ← h.1, hx, D.residue_add_period, dn_res_p]
    · rw [dnG_head, D.naturalLift_head h, hy, D.residue_add_period, dn_res_p1]
  have hlt : x < y := (D.naturalLift_boundary h).2
  exact periodicSwap_boundary_forward n _ hn _
    (D.deleteCorner e (D.strict_corner e he)).boundary_add_period
    (D.dn_R_same e he heq hb) (D.dn_R_avoid e f he hf hcontact hgap) x y ⟨hbR, hlt, hnb⟩

include he hf hcontact heq hb hgap in
theorem dn_geo_bounds {ε : Edge D.area} (hεe : ε ≠ e) (hεg : ε ≠ D.dnG e he heq) {x y : ℤ}
    (h : D.naturalLift ε x y) :
    0 < periodicSwap n (e.head.val : ℤ) y - periodicSwap n (e.head.val : ℤ) x ∧
      periodicSwap n (e.head.val : ℤ) y - periodicSwap n (e.head.val : ℤ) x < n := by
  have hg := D.dn_geo e f he hf hcontact heq hb hgap hεe hεg h
  have := (D.deleteCorner e (D.strict_corner e he)).self_sub_period_lt_boundary
    (periodicSwap n (e.head.val : ℤ) y)
  constructor <;> lia

include he hf hcontact hns hgap in
theorem dn_strict_fix {s : Edge D.area} (hs : s ∈ D.strict) (hse : s ≠ e) (hsf : s ≠ f) :
    s.tail ≠ e.head ∧ s.tail ≠ D.area.next e.head ∧ s.head ≠ e.head ∧
      s.head ≠ D.area.next e.head := by
  have hsh : s.head ≠ e.head := fun h => hse (D.strict_edge_eq_of_head_eq hs he h)
  refine ⟨?_, ?_, hsh, hns s hs⟩
  · intro h
    exact hsf (D.strict_edge_eq_of_tail_eq hs hf (h.trans hcontact.symm))
  · intro h
    have ht := D.strictEdge_tail_boundary hs
    have hR := D.dn_R_boundary e he (s.head.val : ℤ)
    rw [Orientation.residue_intCast_eq, ite_eq_right hsh, add_zero] at hR
    rw [ht, ← hR, ← D.dn_res_p1 e] at h
    obtain ⟨k, hk⟩ := D.residue_eq_exists_period h
    exact D.dn_R_avoid e f he hf hcontact hgap _ k hk


/-- The base normal pairs: every normal pair except the two local normal pairs. -/
noncomputable def dnB : Finset (Fin n × Fin n) :=
  (D.pairGraph.normalEdges.erase (e.head, D.area.next e.head)).erase
    (D.area.next e.head, f.head)

theorem mem_dnB_iff (x : Fin n × Fin n) :
    x ∈ D.dnB e f ↔ x ≠ (D.area.next e.head, f.head) ∧ x ≠ (e.head, D.area.next e.head) ∧
      ∃ ε ∈ D.edgeData.normalEdges, (ε.tail, ε.head) = x := by
  rw [dnB, Finset.mem_erase, Finset.mem_erase, D.mem_pairGraph_normal_iff]

theorem dnB_subset : D.dnB e f ⊆ D.pairGraph.normalEdges := fun x hx =>
  (D.mem_pairGraph_normal_iff x).mpr ((D.mem_dnB_iff e f x).mp hx).2.2

theorem swapVertexPair_swapVertexPair (a b : Fin n) (x : Fin n × Fin n) :
    swapVertexPair a b (swapVertexPair a b x) = x := by
  simp [swapVertexPair_apply]

include he hf hcontact heq hb hns hgap in
theorem dn_swap_mem_dnB {x : Fin n × Fin n} (hx : x ∈ D.dnB e f) :
    swapVertexPair e.head (D.area.next e.head) x ∈ D.dnB e f := by
  rw [mem_dnB_iff] at hx ⊢
  obtain ⟨hxh, hxg, ε, hεN, rfl⟩ := hx
  have hεs : ε ∉ D.strict := (D.mem_normalEdges_iff ε).mp hεN
  have hεe : ε ≠ e := fun h => hεs (h ▸ he)
  have hεg : ε ≠ D.dnG e he heq := fun h => hxg (by rw [h, dnG_tail, dnG_head])
  have hl := D.naturalLift_base ε
  have hgeo := D.dn_geo e f he hf hcontact heq hb hgap hεe hεg hl
  have hvalid : D.boundaryNaturalLift (periodicSwap n (e.head.val : ℤ) (ε.tail.val : ℤ))
      (periodicSwap n (e.head.val : ℤ) ((ε.tail.val : ℤ) + ε.length.val)) :=
    ⟨(D.dn_boundary_le_R e he _).trans hgeo.1, hgeo.2.1⟩
  have hl' := D.edgeFromLift_naturalLift hvalid
  set ε' := D.edgeFromLift _ _ hvalid with hε'
  have ht' : ε'.tail = Equiv.swap e.head (D.area.next e.head) ε.tail := by
    rw [hε', D.edgeFromLift_tail, D.dn_res_swap e he hb, hl.1]
  have hh' : ε'.head = Equiv.swap e.head (D.area.next e.head) ε.head := by
    rw [hε', D.edgeFromLift_head, D.dn_res_swap e he hb, ← D.naturalLift_head hl]
  have hIY := D.dn_Y_ne_I e he hb
  have hAI : e.tail ≠ e.head := e.tail_ne_head
  have hAY := D.dn_A_ne_Y e he hb
  have hZI := D.dn_Z_ne_I e f hcontact
  have hZY := D.dn_Z_ne_Y e f hf hns
  have hpair : swapVertexPair e.head (D.area.next e.head) (ε.tail, ε.head) =
      (ε'.tail, ε'.head) := by
    rw [swapVertexPair_apply, ht', hh']
  rw [hpair]
  refine ⟨?_, ?_, ε', ?_, rfl⟩
  · -- not the pair `y → z`
    intro h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    rw [ht', Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h1
    rw [hh', Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne hZI hZY] at h2
    apply hεs
    have : ε = f := D.edge_eq_of_endpoints (h1.trans hcontact.symm) h2
    exact this ▸ hf
  · -- not the bridge pair `i → y`
    intro h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have hεg' : ε' = D.dnG e he heq :=
      D.edge_eq_of_endpoints (h1.trans (D.dnG_tail e he heq).symm)
        (h2.trans (D.dnG_head e he heq).symm)
    have hglen : ((D.dnG e he heq).length.val : ℤ) = 1 := by
      have := (D.dnG_lift e he heq).2
      lia
    apply hgeo.2.2
    have hres : D.residue (periodicSwap n (e.head.val : ℤ) (ε.tail.val : ℤ)) =
        D.residue (e.head.val : ℤ) := by
      rw [hl'.1, hεg', dnG_tail, dn_res_p]
    obtain ⟨k, hk⟩ := D.residue_eq_exists_period hres
    refine ⟨k, hk, ?_⟩
    rw [hl'.2, hεg', hglen, hk]
    ring
  · -- normal
    rw [mem_normalEdges_iff]
    intro hs'
    by_cases hee : ε' = e
    · have h1 : ε.tail = e.tail := by
        have := ht'
        rw [hee, eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne hAI hAY] at this
        exact this
      have h2 : ε.head = D.area.next e.head := by
        have := hh'
        rw [hee, eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at this
        exact this
      have hlen1 := Edge.length_succ_of_next_head h1 h2
      have hle := ε.length_le_area
      rw [h2, heq, ← D.dn_Le e he, hlen1] at hle
      exact Nat.not_succ_le_self _ hle
    by_cases hff : ε' = f
    · apply hxh
      have h1 : ε.tail = D.area.next e.head := by
        have := ht'
        rw [hff, hcontact, eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at this
        exact this
      have h2 : ε.head = f.head := by
        have := hh'
        rw [hff, eq_comm, Equiv.swap_apply_eq_iff,
          Equiv.swap_apply_of_ne_of_ne hZI hZY] at this
        exact this
      rw [h1, h2]
    · obtain ⟨t1, t2, t3, t4⟩ := D.dn_strict_fix e f he hf hcontact hns hgap hs' hee hff
      apply hεs
      have h1 : ε.tail = ε'.tail := by
        rw [Equiv.swap_apply_eq_iff.mp ht'.symm, Equiv.swap_apply_of_ne_of_ne t1 t2]
      have h2 : ε.head = ε'.head := by
        rw [Equiv.swap_apply_eq_iff.mp hh'.symm, Equiv.swap_apply_of_ne_of_ne t3 t4]
      have : ε = ε' := D.edge_eq_of_endpoints h1 h2
      exact this ▸ hs'

include he hf hcontact heq hb hns hgap in
theorem dnB_map_swap :
    (D.dnB e f).map (swapVertexPair e.head (D.area.next e.head)) = D.dnB e f := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact D.dn_swap_mem_dnB e f he hf hcontact heq hb hns hgap hy
  · intro hx
    refine Finset.mem_map.mpr ⟨_, D.dn_swap_mem_dnB e f he hf hcontact heq hb hns hgap hx,
      swapVertexPair_swapVertexPair _ _ x⟩


/-- The strict endpoint pairs of the DN target, written in source terms. -/
noncomputable def dnSt' : Finset (Fin n × Fin n) :=
  insert (D.area.next e.head, f.head) (insert (e.tail, D.area.next e.head)
    ((D.pairGraph.strictEdges.erase (e.tail, e.head)).erase (e.head, f.head)))

include he in
theorem dn_e_pair : (e.tail, e.head) ∈ D.pairGraph.strictEdges :=
  (D.mem_pairGraph_strict_iff _).mpr ⟨e, he, rfl⟩

include hf hcontact in
theorem dn_f_pair : (e.head, f.head) ∈ D.pairGraph.strictEdges :=
  (D.mem_pairGraph_strict_iff _).mpr ⟨f, hf, by rw [hcontact]⟩

include he hb in
theorem dn_swap_pair_eq (x y : ℤ) :
    (D.residue (periodicSwap n (e.head.val : ℤ) x),
        D.residue (periodicSwap n (e.head.val : ℤ) y)) =
      swapVertexPair e.head (D.area.next e.head) (D.residue x, D.residue y) := by
  rw [swapVertexPair_apply, D.dn_res_swap e he hb, D.dn_res_swap e he hb]

include he hf hcontact heq hb hns hgap in
theorem dn_swap_fwd (Q : Finset (Fin n × Fin n)) (hQ : Q ⊆ D.dnB e f) {x y : ℤ}
    (h : D.pairStep (D.pairGraph.strictEdges ∪ Q) x y) :
    D.pairStep (D.dnSt' e f ∪ Q.map (swapVertexPair e.head (D.area.next e.head)))
      (periodicSwap n (e.head.val : ℤ) x) (periodicSwap n (e.head.val : ℤ) y) := by
  obtain ⟨hmem, h1, h2⟩ := h
  have hres := D.dn_swap_pair_eq e he hb x y
  have hIY := D.dn_Y_ne_I e he hb
  have hAI : e.tail ≠ e.head := e.tail_ne_head
  have hAY := D.dn_A_ne_Y e he hb
  have hZI := D.dn_Z_ne_I e f hcontact
  have hZY := D.dn_Z_ne_Y e f hf hns
  obtain ⟨ε, hεmem, hεp⟩ : ∃ ε : Edge D.area, (ε ∈ D.strict ∨
      (ε ∉ D.strict ∧ (ε.tail, ε.head) ∈ Q)) ∧
      (ε.tail, ε.head) = (D.residue x, D.residue y) := by
    rcases Finset.mem_union.mp hmem with hs | hq
    · obtain ⟨ε, hε, hp⟩ := (D.mem_pairGraph_strict_iff _).mp hs
      exact ⟨ε, Or.inl hε, hp⟩
    · obtain ⟨ε, hε, hp⟩ := (D.mem_pairGraph_normal_iff _).mp (D.dnB_subset e f (hQ hq))
      exact ⟨ε, Or.inr ⟨(D.mem_normalEdges_iff ε).mp hε, hp ▸ hq⟩, hp⟩
  obtain ⟨hεt, hεh⟩ := Prod.mk.inj hεp
  have hl : D.naturalLift ε x y := D.naturalLift_of_residues hεt.symm hεh.symm h1 h2
  by_cases hee : ε = e
  · rw [hee] at hεt hεh hl
    have hsx : periodicSwap n (e.head.val : ℤ) x = x :=
      D.dn_ps_fix e he hb (hεt ▸ hAI) (hεt ▸ hAY)
    have hsy : periodicSwap n (e.head.val : ℤ) y = y + 1 := D.dn_ps_I e he hb hεh.symm
    have hLe := D.dn_Le e he
    have hy := hl.2
    refine ⟨?_, ?_, ?_⟩
    · rw [hres, ← hεt, ← hεh, swapVertexPair_apply, Equiv.swap_apply_of_ne_of_ne hAI hAY,
        Equiv.swap_apply_left]
      exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    · rw [hsx, hsy]; lia
    · rw [hsx, hsy]; lia
  · have hεg : ε ≠ D.dnG e he heq := by
      rintro rfl
      rcases hεmem with hs | ⟨_, hq⟩
      · exact D.dnG_not_strict e he heq hns hs
      · have := ((D.mem_dnB_iff e f _).mp (hQ hq)).2.1
        rw [dnG_tail, dnG_head] at this
        exact this rfl
    have hgb := D.dn_geo_bounds e f he hf hcontact heq hb hgap hee hεg hl
    refine ⟨?_, hgb.1, hgb.2⟩
    rw [hres, ← hεp]
    rcases hεmem with hs | ⟨_, hq⟩
    · apply Finset.mem_union_left
      by_cases hff : ε = f
      · rw [hff, hcontact, swapVertexPair_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne hZI hZY]
        exact Finset.mem_insert_self _ _
      · obtain ⟨t1, t2, t3, t4⟩ := D.dn_strict_fix e f he hf hcontact hns hgap hs hee hff
        rw [swapVertexPair_apply, Equiv.swap_apply_of_ne_of_ne t1 t2,
          Equiv.swap_apply_of_ne_of_ne t3 t4]
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_,
          (D.mem_pairGraph_strict_iff _).mpr ⟨ε, hs, rfl⟩⟩⟩
        · intro h
          exact hff (D.endpointEmbedding.injective (h.trans (by
            change _ = (f.tail, f.head)
            rw [hcontact])))
        · intro h
          exact hee (D.endpointEmbedding.injective h)
    · exact Finset.mem_union_right _ (Finset.mem_map_of_mem _ hq)

include he hf hcontact heq hb hns hlen hgap in
theorem dn_swap_bwd (Q : Finset (Fin n × Fin n)) (hQ : Q ⊆ D.dnB e f) {x y : ℤ}
    (h : D.pairStep (D.dnSt' e f ∪ Q.map (swapVertexPair e.head (D.area.next e.head))) x y) :
    D.pairStep (D.pairGraph.strictEdges ∪ Q)
      (periodicSwap n (e.head.val : ℤ) x) (periodicSwap n (e.head.val : ℤ) y) := by
  obtain ⟨hmem, h1, h2⟩ := h
  have hres := D.dn_swap_pair_eq e he hb x y
  have hIY := D.dn_Y_ne_I e he hb
  have hAI : e.tail ≠ e.head := e.tail_ne_head
  have hAY := D.dn_A_ne_Y e he hb
  have hZI := D.dn_Z_ne_I e f hcontact
  have hZY := D.dn_Z_ne_Y e f hf hns
  have hLe := D.dn_Le e he
  have hLf := f.length_lt_n
  rcases Finset.mem_union.mp hmem with hs | hq
  · rw [dnSt', Finset.mem_insert, Finset.mem_insert, Finset.mem_erase, Finset.mem_erase] at hs
    rcases hs with h | h | ⟨hne1, hne2, hst⟩
    · obtain ⟨hx, hy⟩ := Prod.mk.inj h
      have hd := D.sub_eq_of_residue_eq (x0 := (e.head.val : ℤ) + 1)
        (y0 := (e.head.val : ℤ) + f.length.val) (hx.trans (D.dn_res_p1 e).symm)
        (hy.trans (D.dn_res_T e f hcontact).symm) h1 h2 (by lia) (by lia)
      have hsx := D.dn_ps_Y e he hb hx
      have hsy := D.dn_ps_fix e he hb (hy ▸ hZI) (hy ▸ hZY)
      refine ⟨?_, ?_, ?_⟩
      · rw [hres, hx, hy, swapVertexPair_apply, Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne hZI hZY]
        exact Finset.mem_union_left _ (D.dn_f_pair e f hf hcontact)
      · rw [hsx, hsy]; lia
      · rw [hsx, hsy]; lia
    · obtain ⟨hx, hy⟩ := Prod.mk.inj h
      have hd := D.sub_eq_of_residue_eq (x0 := (e.head.val : ℤ) - e.length.val)
        (y0 := (e.head.val : ℤ) + 1) (hx.trans (D.dn_res_a e).symm)
        (hy.trans (D.dn_res_p1 e).symm) h1 h2 (by lia) (by lia)
      have hsx := D.dn_ps_fix e he hb (hx ▸ hAI) (hx ▸ hAY)
      have hsy := D.dn_ps_Y e he hb hy
      refine ⟨?_, ?_, ?_⟩
      · rw [hres, hx, hy, swapVertexPair_apply, Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne hAI hAY]
        exact Finset.mem_union_left _ (D.dn_e_pair e he)
      · rw [hsx, hsy]; have := e.length_pos; lia
      · rw [hsx, hsy]; lia
    · obtain ⟨s, hs', hp⟩ := (D.mem_pairGraph_strict_iff _).mp hst
      have hse : s ≠ e := by
        rintro rfl
        exact hne2 hp.symm
      have hsf : s ≠ f := by
        rintro rfl
        apply hne1
        rw [← hp, hcontact]
      have hsg : s ≠ D.dnG e he heq := by
        rintro rfl
        exact D.dnG_not_strict e he heq hns hs'
      obtain ⟨hpt, hph⟩ := Prod.mk.inj hp
      have hl : D.naturalLift s x y := D.naturalLift_of_residues hpt.symm hph.symm h1 h2
      have hgb := D.dn_geo_bounds e f he hf hcontact heq hb hgap hse hsg hl
      refine ⟨?_, hgb.1, hgb.2⟩
      obtain ⟨t1, t2, t3, t4⟩ := D.dn_strict_fix e f he hf hcontact hns hgap hs' hse hsf
      rw [hres, ← hp, swapVertexPair_apply, Equiv.swap_apply_of_ne_of_ne t1 t2,
        Equiv.swap_apply_of_ne_of_ne t3 t4]
      exact Finset.mem_union_left _ ((D.mem_pairGraph_strict_iff _).mpr ⟨s, hs', rfl⟩)
  · obtain ⟨q, hqQ, hqe⟩ := Finset.mem_map.mp hq
    have hB : (D.residue x, D.residue y) ∈ D.dnB e f :=
      hqe ▸ D.dn_swap_mem_dnB e f he hf hcontact heq hb hns hgap (hQ hqQ)
    obtain ⟨_, hn2, ε, hεN, hp⟩ := (D.mem_dnB_iff e f _).mp hB
    have hεs : ε ∉ D.strict := (D.mem_normalEdges_iff ε).mp hεN
    have hεe : ε ≠ e := fun h => hεs (h ▸ he)
    have hεg : ε ≠ D.dnG e he heq := by
      rintro rfl
      apply hn2
      rw [← hp, dnG_tail, dnG_head]
    obtain ⟨hpt, hph⟩ := Prod.mk.inj hp
    have hl : D.naturalLift ε x y := D.naturalLift_of_residues hpt.symm hph.symm h1 h2
    have hgb := D.dn_geo_bounds e f he hf hcontact heq hb hgap hεe hεg hl
    refine ⟨?_, hgb.1, hgb.2⟩
    rw [hres, ← hqe, swapVertexPair_swapVertexPair]
    exact Finset.mem_union_right _ hqQ

include he hf hcontact heq hb hns hlen hgap in
theorem dn_swap_step (Q : Finset (Fin n × Fin n)) (hQ : Q ⊆ D.dnB e f) (x y : ℤ) :
    D.pairStep (D.pairGraph.strictEdges ∪ Q) x y ↔
      D.pairStep (D.dnSt' e f ∪ Q.map (swapVertexPair e.head (D.area.next e.head)))
        (periodicSwap n (e.head.val : ℤ) x) (periodicSwap n (e.head.val : ℤ) y) := by
  refine ⟨D.dn_swap_fwd e f he hf hcontact heq hb hns hgap Q hQ, fun h => ?_⟩
  have hi := periodicSwap_involutive n (e.head.val : ℤ) (D.dn_two_le e he hb)
  have := D.dn_swap_bwd e f he hf hcontact heq hb hns hlen hgap Q hQ h
  rwa [hi x, hi y] at this


end DN

end Diagram

end VerticalStripLLT.Circular

