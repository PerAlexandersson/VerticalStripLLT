# Finite companion lemma for complete circular flip components

Status: complete mathematical proof, audited independently by primary, Astra
and Terra. The full companion is not yet a Lean theorem. No enumeration was
used. Aristotle supplied the coefficient proof; primary removed an unused
incorrect claim about unscaled integer strict potentials and supplied the
explicit finite component-isolation argument below.

This replaces the polyhedral step in the
[Overleaf comparison](COMPONENT_CIRCULAR_FACE_PROOF.md). The ordinary component
proof and compatible-lift transport remain the inputs stated there.
Request and output provenance are recorded in [the ledger](../ARISTOTLE.md).

We work with a finite acyclic selected graph R with positive integer natural
edge lengths. We call F balanced when these lengths are differences of an
integer potential p on each weak F-component. For balanced F⊆X, contract its
weak components, retaining every edge of X\F, including loops and parallel
edge instances. The gain of u→v is δ=ℓ−(p_v−p_u). We set

    κ_X(F) = (−1)^(c(F)−c(X))

when every directed contracted cycle has negative gain and every contracted
weak component is strongly connected; otherwise κ_X(F)=0. We also set it
to zero for unbalanced F or F⊈X. Changes of p by componentwise constants
preserve all cycle gains, so the coefficient is well-defined.

`V` is the fixed vertex set, and `c(X)` is the number of
weak components of the spanning graph `(V, X)`, isolated vertices included. `W` stands
for either semantics: `W(X) = K(X)`, or `W(X) = [H_X]` in the free abelian group on
entire periodic maps. For `E`, apply the linear map `[H] ↦ E` to the second case.

The coefficient proof uses the following already proved input:

* **(DR) the deletion recurrence.** Suppose `R` is unbalanced, `C` is an unbalanced cycle
  of `R` oriented so that `Σ_P ℓ > Σ_N ℓ`, and `B = R \ N`. Then
  `Σ_{J⊆N} (-1)^{|J|} W(B∪J) = 0`.

It does not use Brianchon–Gram, valuations, Euler characteristics of polyhedra, or nerve
theorems.

---

If R is unbalanced, we choose a spanning forest and propagate an integer
potential along its edges. Some remaining edge violates its potential equation;
its fundamental undirected cycle has nonzero signed length. We orient that
traversal to make the signed excess positive. Both P and N are nonempty,
since otherwise R would contain a directed cycle. Thus every deletion child
with J properly contained in N has strictly fewer edges.

## 0. Reduction to one coefficient identity (**)

**Claim (**).** Let `R`, `C`, `P`, `N` and `B` be as in (DR). For every `F ⊆ R`,

    Σ_{J⊆N} (-1)^{|J|} κ_{B∪J}(F) = 0,            with κ_X(F) := 0 when F ⊄ X.

**(**) implies the theorem.** We use strong induction on `|R|`.

*Balanced `R`.* Then `κ_R(F) = [F = R]`, so the identity is trivial.

* `F = R` is good. The gain graph has no edges, so (i) holds vacuously, and every block
  contracts to a single vertex, so (ii) holds. The sign is `(-1)^0 = 1`.
* A balanced `F ⊊ R` is not good. Condition (i) does not depend on translations of `p`
  on `F`-blocks, so we may use the restriction of an `R`-potential. Then `δ_e = 0` on
  every edge of `R \ F`. Pick such an edge `e`. By (ii), its contracted `R`-block is
  strongly connected, so `e` is a loop or lies on a directed cycle. That cycle has gain
  `0`, so (i) fails.

*Unbalanced `R`.* Choose any `C`. By (DR),
`W(R) = −(-1)^{|N|} Σ_{J⊊N} (-1)^{|J|} W(B∪J)`. Each `B∪J` with `J ⊊ N` is a proper
subgraph, so the induction hypothesis expands it. Collecting the coefficient of `W(F)`
gives `−(-1)^{|N|} Σ_{J⊊N} (-1)^{|J|} κ_{B∪J}(F)`. By (**) this equals
`(-1)^{2|N|} κ_R(F) = κ_R(F)`.

The coefficients are fixed in advance. Since (**) holds for **every** admissible cycle,
the result does not depend on the order of deletions. Confluence is never needed.

## 1. Moving (**) into the contracted gain graph

Fix `F`. If `F` is unbalanced, every term is 0, so assume `F` is balanced. Fix one
compatible potential `p`. Let `Γ` be the multigraph with vertex set `V'`, the set of
`F`-blocks. Its edges are `R \ F` (loops allowed), with gains
`δ_e = ℓ_e − (p_v − p_u)`. Split these edges into:

* the required edges `E_B := B \ F`;
* the optional edges `N' := N \ F`.

The terms of (**) with `J ⊉ J₀ := F ∩ N` vanish. Write `J = J₀ ⊔ J'`, where `J' ⊆ N'`.
Contracting `F` does not change weak components, so `c(B∪J) = c(Γ_{J'})`, where
`Γ_{J'} := (V', E_B ∪ J')`. Remove the constant factor `(-1)^{|J₀|+c(F)}`. Then (**)
becomes

    (**')   Σ_{J'⊆N'} (-1)^{|J'|} (-1)^{c(Γ_{J'})} [neg(J') ∧ tc(J')] = 0,

with the following notation:

* `neg(J')`: every directed cycle of `Γ_{J'}` has gain `< 0`. This is (i).
* `tc(J')`: every edge of `Γ_{J'}` lies on a directed cycle. This is equivalent to (ii),
  "every weak component is strongly connected".

**The excess walk.** The cycle `C` projects to a closed walk `C'` in `Γ`:

* each edge of `P' := P \ F` (all in `E_B`) is traversed forward;
* each edge of `N'` is traversed backward, exactly once;
* the edges of `F` collapse.

Since `δ = 0` on `F` and `p` telescopes around `C`,

    D := Σ_{P'} δ − Σ_{N'} δ = Σ_P ℓ − Σ_N ℓ ≥ 1.

This walk is the only feature of `C` that the rest of the proof uses.

## 2. Linearising strong connectivity: ordered partitions

**Lemma A.** Let `G` be a finite digraph on `V'`, loops allowed. Call an ordered set
partition `ω = (β_1, …, β_r)` of `V'` *compatible* with `G` when every edge `x→y` has
`lev(x) ≤ lev(y)`. Then

    Σ_{ω compatible} (-1)^{|ω|} = (-1)^{c(G)} [tc(G)].

*Proof.*

1. **Reduction to the condensation.** Every edge of a directed cycle must stay in one
   level, so each strong component lies in one block. This gives a bijection between
   compatible `ω` and ordered partitions of the condensation DAG `H` that are compatible
   with `H`, and the bijection preserves `r`. Moreover, `H` has no edges exactly when
   `tc(G)` holds, and in that case #strong components `= c(G)`. So it suffices to prove
   `f(H) := Σ (-1)^{|ω|} = (-1)^{|V(H)|} [H has no edges]` for a DAG `H`.
2. **Recursion.** Peel off the top block `U`. It is a nonempty up-closed set, and the
   remaining blocks form a compatible partition of `H − U`. Hence
   `f(H) = −Σ_{∅≠U up-closed} f(H−U)`, with `f(∅) = 1`.
3. **Characterising the relevant `U`.** Let `M` be the set of heads of edges. A set `U`
   is up-closed with `H − U` edgeless exactly when `M ⊆ U`.
4. **Induction.** By induction,
   `f(H) = −(-1)^{|V|} Σ_{U⊇M, U≠∅} (-1)^{|U|}`.
   * The sum over all `U ⊇ M` is 0, because `M ≠ V`: a nonempty DAG has a source.
   * The term for `U = ∅` is present only when `M = ∅`.

   So `f(H) = (-1)^{|V|} [M = ∅]`. ∎

**Applying Lemma A.** Apply it to `G = Γ_{J'}` and swap the order of summation. The
left side of (**') becomes

    Σ_ω (-1)^{|ω|} Σ_{J' ∈ Δ_ω} (-1)^{|J'|},
    Δ_ω := { J' ⊆ N' : E_B ∪ J' compatible with ω, neg(J') }.

It is enough to show that every inner sum vanishes. `Δ_ω` is down-closed.

* **Case 1: some `N'` edge `e` is compatible and strictly upward.** Every directed cycle
  of a graph compatible with `ω` stays in one level, so `e` lies on no cycle. Therefore
  `J' ↦ J' △ {e}` is a sign-reversing involution of `Δ_ω`, and the inner sum is 0.
* **Case 2: otherwise.** Follow `lev` along `C'`:
  * each `P'` step changes `lev` by `≥ 0`;
  * each backward step over a compatible `N'` edge changes it by `0`, since such edges
    are level in this case;
  * each backward step over an incompatible `N'` edge changes it by `> 0`.

  The total change is `0`. So every `N'` edge is compatible and level, and `C'` lies in
  one level. Then `Δ_ω = {J' ⊆ N' : neg(J')}`, which is exactly Lemma X below.

(If `E_B` is not compatible with `ω`, then `Δ_ω = ∅`.)

## 3. Lemma X: the canonical-potential involution

**Lemma X.** `Σ_{J'⊆N', neg(J')} (-1)^{|J'|} = 0`.

*Proof.* Let `r = |V'|` and choose an integer `M > max(r, |N'|)`. Put `γ_f := M δ_f + 1`.

**Step 1: `neg(J')` holds exactly when `Γ_{J'}` has no γ-cycle of positive gain.** A
simple cycle of length `L ≤ r` has γ-gain `M Σδ + L`:

* if `Σδ ≤ −1`, the γ-gain is `≤ −M + r < 0`;
* if `Σδ ≥ 0`, the γ-gain is `≥ 1`.

Closed walks split into simple cycles.

**Step 2: the canonical potential.** Suppose `neg(J')` holds. Let `t^{J'}_y` be the
maximum of `0` and the γ-gains of all directed walks in `Γ_{J'}` that end at `y`. This is
finite, and it is the **least** `t ≥ 0` with `t_y − t_x ≥ γ_f` on every edge of
`Γ_{J'}`. Let

    S(J') := { e = u→v ∈ N' : t^{J'}_v − t^{J'}_u > γ_e }

be the set of strictly slack optional edges, whether present or absent.

**Step 3: `S(J')` is nonempty.** The potential `t^{J'}` telescopes around `C'`, so

    Σ_{N'} slack = Σ_{P'} slack + (Σ_{P'}γ − Σ_{N'}γ).

Here `Σ_{P'} slack ≥ 0`, because `P' ⊆ E_B`. Also
`Σ_{P'}γ − Σ_{N'}γ = M·D + |P'| − |N'| > 0`. So some edge of `N'` is strictly slack.

**Step 4: toggling `e ∈ S(J')` does not change the potential.**

* *Adding `e`.* `t^{J'}` stays feasible and `≥ 0`, so no positive cycle appears. By
  minimality, `t^{J'∪e} ≤ t^{J'}`. Having more walks gives `≥`. So the two are equal.
* *Removing `e`.* Take a walk `α e β` ending at `y`. Its gain is at most
  `t_u + γ_e + g(β) < t_v + g(β) ≤ t_y`. So no maximizing walk uses `e`. Maximizers
  exist, because simple paths suffice. Hence `t^{J'∖e} = t^{J'}`.

In both cases `J' △ {e}` satisfies `neg`, and `S` is unchanged.

**Step 5: the involution.** `J' ↦ J' △ {min S(J')}` is therefore a fixed-point-free,
sign-reversing involution of `{J' : neg(J')}`. ∎

This proves (**'), hence (**), hence

    K(R) = Σ_{F⊆R} κ_R(F) K(F),   [H_R] = Σ_{F⊆R} κ_R(F) [H_F],   and likewise for E.

## Whole-component isolation without geometry

We first use the previously proved universal-ambient reduction to work in
the unmarked complete circular diagram. Each original component stays an
entire component, with both valuations unchanged. Let C be such a component.
For a balanced F define

    a_C(F) = Σ_(R∈C) κ_R(F).

We prove that a_C is constant along every actual flip F↔F′. Write that flip
as ab↔bc retaining ac, with a<b<c<a+n in the integer lift. For each good
pair (R,F), choose an integer compatible potential p on F. In the contracted
gain graph choose M larger than its vertex count and use the canonical
integer potential for γ=Mδ+1 constructed in Lemma X. The rational assignment

    z_v = p_v + t_[v]/M

has equality z_v−z_u=ℓ on F and strict inequality on R\F. Negative cycle
gains guarantee this construction; unscaled integer strict shifts are neither
claimed nor needed.

The triangle lengths satisfy ℓ(ac)=ℓ(ab)+ℓ(bc). Hence the equations of F
and F′ have exactly the same solutions. Their weak partitions also agree.
The edge bc cannot lie in R: it is absent from F but its equation is forced
by the tight edges ab and ac, contradicting strict slack on R\F. Set
R′=R−ab+bc. The same z satisfies every selected edge of R′ with a positive
coordinate increase, so R′ is acyclic.

We must prove that this is an actual flip in the original component C.
Consider a competing integer lifted path between the displayed endpoints of
ab or ac in R. Its natural lengths sum to the displayed integer displacement.
The z-differences telescope on endpoint residues and have the same total,
because the displayed edge is tight. Every slack is nonnegative, so every
path edge has zero slack and belongs to F. A competing intermediate lifted
vertex would therefore contradict the full integer cover condition for F.
This proves the source covers in R. The same reasoning proves the target
covers in R′ from F′. The absent short edge cannot be a cover because every
cover is an actual selected lifted edge. Thus R↔R′ is an actual flip and
R′ belongs to the original C. No no-wrap assumption enters this argument.

Finally, R\F=R′\F′ and the same p works for F and F′. Their contracted gain
multigraphs are literally equal, so both goodness conditions agree. Their
weak component counts and signs agree as well. Reversing the exchange
recovers R. This is the required coefficient-preserving bijection, proving
a_C(F)=a_C(F′). Balancedness itself is preserved along these flips.

Summing the canonical expansion over C and grouping by entire balanced
components B therefore gives, with the SAME integer coefficients,

    K(C)=Σ_B a_(C,B) K(B),    E(C)=Σ_B a_(C,B) E(B).

Compatible lifts identify each whole balanced component with an ordinary
component. The ordinary component formula K(B)=E(B) now proves K(C)=E(C).
The selected-normal-edge count is constant on each original component, so
restoring its q-weight gives the full component HRV formula and e-positivity.
This completes the finite companion proof.

## Lean decomposition

The abstract contracted-gain identity (**′**) is now Lean-verified as
`GainData.sum_powerset_cyclicNegative_eq_zero_of_gain_excess` in
`Components/GainCoefficientCancellation.lean`. It retains the original edge
instances and proves both total-cyclicity and negative-cycle conditions with
the weak-component parity sign. `PartitionConnectivity` proves Lemma A;
`GainLevels` handles the two fixed-level cancellation cases. Actual balanced-F
contraction and the subsequent W/component assembly remain unformalized.

We can formalize this argument with finite graphs and integer arithmetic.
The main independent statements are:

1. The ordered-partition identity of Lemma A, including the empty graph.
   A convenient representation is a surjective map V→Fin k with
   0≤k≤|V|; k=0 must be allowed when V is empty. No quotient of arbitrary
   lists or symmetric-function infrastructure is required.
2. Canonical longest-walk potentials for graphs with strictly negative cycles.
   We may maximize over simple paths after deleting negative closed walks.
3. The strict-slack edge toggle and the signed subset cancellation of Lemma X.
4. The per-F coefficient recurrence and induction on the number of edges.
5. The finite tight-edge flip reconstruction above and grouping by complete
   components. This preserves the original component throughout.

Related Lean: `Components/BlockCancellation.lean` proves the ordinary
unique-sink cancellation. `Components/WordRank.lean` and `LiftCoverRank.lean`
connect compatible words to the actual integer cover relation. The existing
`Circular/Flip.lean` supplies `DirectedFlipWitness`, `flipComponent`, and
`target_eq_source_swap`. These are verified ingredients, not a declaration
of the full companion theorem.

## Remarks

* **Where the known shortcuts fail.** A direct single-edge toggle on good sets does not
  work. Suppose `N'` has two edges running in opposite directions between two strongly
  connected components `A` and `A'`. Then `∅` and `N'` are both good, but no single
  toggle connects them. Lemma A removes this obstruction by turning strong connectivity
  into an alternating sum of down-closed conditions. After that, the HRV-style argument
  (toggle the least strictly slack optional edge) works with the canonical least
  potential `t^{J'}` in place of a fixed coloring.
