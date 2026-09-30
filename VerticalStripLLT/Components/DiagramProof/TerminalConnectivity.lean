import VerticalStripLLT.Components.DiagramProof.RepairedTerminalTransfer
import VerticalStripLLT.Components.DiagramProof.TerminalReceiver
import VerticalStripLLT.Components.DiagramProof.OccupancyCounts
import VerticalStripLLT.Components.DiagramProof.EqualSumCounts
import VerticalStripLLT.Components.DiagramProof.OccupancyTransfers
import VerticalStripLLT.Components.DiagramProof.Preparation

/-! Connected fixed-size states when the last clique contains all chain terminals. -/

namespace VerticalStripLLT.Circular.DiagramProof.CornerFamily

variable {n : ℕ} {D : Diagram n} (F : CornerFamily D) (hforward : Forward D)

/-- Connected anchors of the same size are in one actual flip component when
the last clique contains every terminal. -/
theorem anchors_connected_of_total_last_clique (c : Edge D.area) (hc : c ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ c.head)
    (hterm : ∀ v, c.tail < F.terminal hforward v)
    (θ τ : Orientation D) (hθ : F.Anchor hforward θ) (hτ : F.Anchor hforward τ)
    (hθconn : SelectedConnected θ) (hτconn : SelectedConnected τ)
    (htotal : totalSelected θ = totalSelected τ) : Relation.ReflTransGen (Flip D) θ τ := by
  classical
  let S := {σ : Orientation D // F.Anchor hforward σ ∧ SelectedConnected σ}
  let count : S → Fin n × Fin n → ℕ := fun σ => F.occupancy hforward σ.val
  let step : S → S → Prop := fun σ η => Relation.ReflTransGen (Flip D) σ.val η.val
  let target : S := ⟨τ, hτ, hτconn⟩
  have hconn (σ : S) : (F.chainQuotient hforward (fullSelection σ.val)).Connected := {
    preconnected := (F.chainQuotient_preconnected_iff_selectedConnected hforward σ.val
      σ.property.1.1).mpr σ.property.2
    nonempty := ⟨F.chainVertex hforward c.head⟩ }
  have hfinish (σ : S) (hcounts : count σ = count target) :
      Relation.ReflTransGen step σ target := by
    apply Relation.ReflTransGen.single
    exact F.anchors_connected_of_occupancy hforward σ.property.1 hτ
      (fun p => congrFun hcounts p)
  have hmove (σ : S) (hsum : (∑ p, count σ p) = ∑ p, count target p)
      (hdiff : ∃ p, count σ p ≠ count target p) :
      ∃ e f, ∃ η : S, count target e < count σ e ∧ count σ f < count target f ∧
        Relation.ReflTransGen step σ η ∧
        ∀ p, count η p = if p = e then count σ p - 1
          else if p = f then count σ p + 1 else count σ p := by
    have hne : count σ ≠ count target := by
      intro h
      obtain ⟨p, hp⟩ := hdiff
      exact hp (congrFun h p)
    obtain ⟨p, q, hp, hq⟩ := exists_surplus_and_deficit_of_sum_eq _ _ hsum hne
    obtain ⟨e, heT, hep⟩ := F.exists_terminalEdge_of_occupancy_gt hforward c
      (fun v => ⟨hterm v, hlast _⟩) σ.val τ σ.property.1 hτ p hp
    obtain ⟨f₀, hf₀T, hfq⟩ := F.exists_terminalEdge_of_occupancy_gt hforward c
      (fun v => ⟨hterm v, hlast _⟩) τ σ.val hτ σ.property.1 q hq
    have he : F.occupancy hforward τ (F.copyLabel hforward e) <
        F.occupancy hforward σ.val (F.copyLabel hforward e) := by
      simpa only [hep] using hp
    have hf₀ : F.occupancy hforward σ.val (F.copyLabel hforward f₀) <
        F.occupancy hforward τ (F.copyLabel hforward f₀) := by
      simpa only [hfq] using hq
    obtain ⟨f, hfT, hf, hef, hfinal⟩ := F.exists_terminal_receiver hforward c
      (fun v => ⟨hterm v, hlast _⟩) σ.val τ σ.property.1 hτ
      (hconn σ) (hconn target) e heT he f₀ hf₀T hf₀
    have hvac := hf.trans_le (F.occupancy_le_capacity hforward τ hτ (F.copyLabel hforward f))
    obtain ⟨η, hση, hη, hupdate⟩ := F.exists_terminal_transfer hforward c hc hlast hterm
      σ.val σ.property.1 e f heT hfT hef (Nat.zero_le _ |>.trans_lt he) hvac
      (hconn σ) hfinal
    let next : S := ⟨η, hη, (selectedConnected_iff_of_reachable hση).mp σ.property.2⟩
    exact ⟨F.copyLabel hforward e, F.copyLabel hforward f, next,
      he, hf, Relation.ReflTransGen.single hση, hupdate⟩
  have hsum : (∑ p, count ⟨θ, hθ, hθconn⟩ p) = ∑ p, count target p := by
    change (∑ p, F.occupancy hforward θ p) = ∑ p, F.occupancy hforward τ p
    rw [F.sum_occupancy, F.sum_occupancy, htotal]
  have hp := reflTransGen_of_occupancy_descent_of_equal_counts count step target
    hfinish hmove hsum
  have flatten {σ η : S} (h : Relation.ReflTransGen step σ η) :
      Relation.ReflTransGen (Flip D) σ.val η.val := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih => exact ih.trans hs
  exact flatten hp

/-- Preparation extends last-clique connectivity to all connected common-cover
states of the same total selected size. -/
theorem commonCover_connected_of_total_last_clique (c : Edge D.area) (hc : c ∈ F.edges)
    (hlast : ∀ v : Fin n, v ≤ c.head)
    (hterm : ∀ v, c.tail < F.terminal hforward v)
    (θ τ : Orientation D) (hθ : F.CommonCover θ) (hτ : F.CommonCover τ)
    (hθconn : SelectedConnected θ) (hτconn : SelectedConnected τ)
    (htotal : totalSelected θ = totalSelected τ) : Relation.ReflTransGen (Flip D) θ τ := by
  obtain ⟨α, hθα, hα, _⟩ := F.exists_preparation hforward θ hθ
  obtain ⟨β, hτβ, hβ, _⟩ := F.exists_preparation hforward τ hτ
  have hαconn := (selectedConnected_iff_of_reachable hθα).mp hθconn
  have hβconn := (selectedConnected_iff_of_reachable hτβ).mp hτconn
  have hsize : totalSelected α = totalSelected β :=
    (totalSelected_eq_of_reachable hθα).symm.trans
      (htotal.trans (totalSelected_eq_of_reachable hτβ))
  have hαβ := F.anchors_connected_of_total_last_clique hforward c hc hlast hterm
    α β hα hβ hαconn hβconn hsize
  exact hθα.trans (hαβ.trans (flip_reachable_symm hτβ))

end VerticalStripLLT.Circular.DiagramProof.CornerFamily
