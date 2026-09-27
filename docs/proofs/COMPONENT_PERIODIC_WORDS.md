# Periodic HRV coefficients and circular word corrections

Status: mathematical lemmas, independently checked by primary and Terra
(periodic coefficients) and primary and Astra (word corrections). These are
not Lean declarations or a proof of the remaining circular component formula.
They identify the exact changes required by the
[ordinary word proof](COMPONENT_ORDINARY_PROOF.md).

## Exact coefficients on the integer cover

Fix a period n>0 and disjoint finite sets N,F of directed edge orbits, each
with positive length less than n. A cyclic selection contributes zero. For
acyclic selections write α_J for the actual lifted HRV map of N∪J, and set

    H(N,F)=Σ_(J⊆F, N∪J projected acyclic) (−1)^(|F|−|J|) [α_J].

The basis here consists of maps on the integer cover, not residue maxima.
Fix α:Z→Z satisfying

    α(z+n)=α(z)+n,       α(z)≥z,       α(α(z))=α(z).

All tests below are made on actual lifted edges u→v, and are independent
of simultaneous translation by n. If an N edge violates α(u)≥α(v), the
coefficient of [α] is zero. Otherwise let U be the set of nonroot residues
u with no N edge u→v satisfying α(u)=α(v). The coefficient is nonzero
exactly when all three conditions hold:

1. Every F edge u→v satisfies α(u)≤α(v).
2. Every equal-α F edge has its tail in U.
3. Each residue in U has an equal-α outgoing F edge.

In that case the coefficient is (−1)^(|F|+|U|). Maps failing the initial
periodicity, extensivity or idempotence tests have coefficient zero.

**Proof.** The local HRV characterization from the ordinary case still holds:
selected edges weakly decrease α, and each nonroot has a same-α selected
outgoing edge. Starting at z, repeatedly follow such edges. Their integer
endpoints strictly increase but stay bounded by α(z), so the process reaches
the root α(z). Conversely, every reachable w satisfies w≤α(w)≤α(z).
Thus this characterization identifies the greatest reachable lift exactly.

It also forces projected acyclicity. A selected projected directed cycle
lifts from z to z+kn for some k>0, whereas monotonicity would give
α(z)≥α(z+kn)=α(z)+kn, a contradiction. Therefore restricting the defining
sum to acyclic selections removes no selection realizing α.

Now group optional choices by their tail residues. Strictly increasing-α
edges are forced absent, strictly decreasing-α edges are free toggles, and
equal-α edges at a tail already supported by N are free toggles. A root
cannot have an equal-α outgoing edge because its endpoint is larger. Every
remaining unsupported tail must select a nonempty subset of its equal-α
optional edges. Its alternating factor is (−1)^(m+1), where m is their
number. Multiplying these independent factors proves the formula, exactly
as in [the ordinary coefficient theorem](COMPONENT_HRV_DIFFERENCES.md).

## Winding changes mixed-cycle cancellation

In the mixed graph M=N∪F^op, every supported α weakly decreases along lifted
mixed paths. A closed projected mixed walk of winding k>0 therefore makes
support impossible. For winding zero, a directed closed lifted walk uses
both forward N and backward F edges. At a transition from reversed F to N,
all α values on the closed walk are equal. The shared vertex must then both
belong to U (from F) and have same-α N support, a contradiction.

Negative winding is different: map coefficients need not vanish. Here is
an exact obstruction to that stronger assertion, not a substitute theorem.
For n=3 take N={0→1} and F={0→2,2→1}, with lengths 1,2,2. The mixed cycle
has lifted form

    0 → 1 → −1 → −3.

All four original selections are projected DAGs. Their lifted HRV triples
at 0,1,2, and their elementary evaluations, are:

| J | (α_J(0),α_J(1),α_J(2)) | Elementary monomial |
| --- | --- | --- |
| empty | (1,1,2) | e₂e₁ |
| {0→2} | (2,1,2) | e₂e₁ |
| {2→1} | (1,1,4) | e₃ |
| F | (4,1,4) | e₃ |

The map (1,1,2), extended periodically, has coefficient +1 in H. Thus H is
nonzero as a sum of lifted maps. Its elementary evaluation is nevertheless
zero: e₂e₁−e₂e₁−e₃+e₃=0. The mixed coloring conditions
c(0)<c(1)≤c(2)≤c(0) likewise have no solutions. A circular companion must
allow cancellation between different HRV maps after fiber evaluation.

## The exact circular four-word correction

Fix cyclically ordered lifts a<b<c<a+n, and a complete component C. Let
m(π;E) count states of C compatible with a permutation π and containing
all directed edges in E. Write m(π)=m(π;empty). In every displayed word,
the same arbitrary exterior words ρ,σ surround the contiguous triple.
Opposite directed pairs, such as ac and ca, are distinct circular edges.
A nonexistent or incompatible edge gives count zero. Then

    m(acb)+m(bca)−m(cab)−m(bac)
      = m(acb;{ac,cb})−m(bac;{ac,ba})
        +m(bca;{ca})−m(cab;{ca}).

First compare adjacent a,c in acb and cab. Their difference counts the
ac-selected states on the first side minus ca-selected states on the second.
The same comparison for bac and bca gives the other two terms. For the
remaining ac-selected difference, pair the sector with cb absent on acb
with the sector with ba absent on bac. When both shorts are absent, retain
the state. Otherwise exchange ab and bc, retaining ac. Interval closure
makes both shorts natural and normal. Contiguity makes their projected
cover tests valid once those backward edges are excluded; hence the lifted
cover tests also hold. The new state has the displayed linear extension,
so it is admissible. It is an actual flip inside the original component.
The unmatched sectors are precisely the four terms on the right.

In an ordinary diagram every correction term vanishes. Circularly this need
not happen, even in a minimum-area, saturated primitive component. With
one-based vertices 1,2,3, take area (1,2,2), strict corners 13,32, and selected
normal 12. The selected relation {12,13,32} is a singleton component: either
potential short exchange creates a directed 2-cycle. Its unique linear
extension is 132, so the left side for a=1,b=2,c=3 is 1. Its two paths
1→2 and 1→3→2 differ by one period, so its winding gcd is 1. The correction
term m(132;{13,32}) is exactly 1.

There is a separate coloring issue. A backward numeric circular edge still
imposes a strict color inequality. Thus the ordinary total-order enumerator,
strict only at numeric ascents, does not refine every circular selected
relation under one fixed labeling. A periodic proof must address both this
coloring convention and the actual lifted HRV statistic; the count identity
alone is not either semantic bridge.

Related Lean: `VerticalStripLLT/Circular/HRV.lean` defines `liftedHRV`, `hrv`
and `hrvMonomial`; `Circular/Flip.lean` defines actual lifted-cover flips.
No source build or enumeration was needed for these mathematical checks.
