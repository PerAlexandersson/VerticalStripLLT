# Exact HRV-map coefficients after alternating edge deletion

Status: the coefficient formula and counting corollary below are proved
mathematical statements, independently audited by primary and Astra; Terra
also audited the strict-corner case. They sharpen the
[corner-difference companion](COMPONENT_CORNER_DIFFERENCES.md). They do not
prove component isolation or the full component theorem, and are not Lean
declarations.

The [complete ordinary component proof](COMPONENT_ORDINARY_PROOF.md) now uses
this coefficient theorem through its labeled-poset and mountain-block
consequences. The historical matching obstructions below remain valid; that
proof does not assume any of the failed pointwise identities.

## A local characterization of a highest-reachability map

All vertices lie in one fixed finite linear order and all edges point forward.
A vertex reaches itself. Let R be an edge set and α a map on its vertices.
Then α is the highest-reachability map of R if and only if:

1. α(v)≥v and α(α(v))=α(v) for every vertex v;
2. α(u)≥α(v) for every selected edge u→v;
3. every nonroot u, meaning α(u)>u, has a selected outgoing edge u→v
   with α(v)=α(u).

Necessity follows by taking the first step on a path to the reachable maximum.
For sufficiency, repeatedly follow a same-α edge from a nonroot. Vertex labels
strictly increase, so the process ends at a root r with r=α(r)=α(u).
Thus the prescribed maximum is reachable. Every other reachable vertex w
satisfies w≤α(w)≤α(u) by conditions 1 and 2, proving exact equality.

## The coefficient formula for arbitrary optional forward edges

Let N and F be disjoint sets of forward edges. For J⊆F write α_J for the
highest-reachability map of N∪J. In the free abelian group on maps define

    H(N,F) = Σ_(J⊆F) (−1)^|F\J| [α_J].

We give the exact coefficient c_α of any fixed map α. If α fails condition 1
above, or some edge of N violates condition 2, then c_α=0. Otherwise define

    U_α = {u : α(u)>u and no edge u→v of N has α(v)=α(u)}.

The remaining conditions for a nonzero coefficient are:

- every edge u→v of F satisfies α(u)≤α(v);
- every equal-α edge of F has its tail in U_α;
- every u∈U_α has at least one equal-α outgoing edge in F.

If these conditions hold, then

    c_α = (−1)^(|F|+|U_α|).

Otherwise c_α=0. In particular every map coefficient belongs to {−1,0,1},
even when several edges of F have the same tail.

To prove this, use the preceding characterization. An edge of F which
strictly increases α cannot be selected, and contributes its absent-edge
sign −1. An edge which strictly decreases α may be freely selected or
omitted without affecting the same-α support condition. Toggling it pairs
opposite signs, giving zero. An equal-α edge at a tail already supported by N
is likewise a free toggle. A root cannot have an equal-α outgoing forward
edge because α(v)≥v>u=α(u).

The only remaining choices occur at the unsupported tails u∈U_α. Each such
tail must select a NONEMPTY subset of its m_u equal-α outgoing F edges.
Choices at different tails are independent. Their local contribution is

    Σ_(∅≠J⊆{1,...,m_u}) (−1)^(m_u−|J|) = (−1)^(m_u+1).

If m_u=0 no choice is possible. Multiplying these factors with the signs of
all forced-absent edges gives exactly the displayed formula.

This also gives another proof of mixed-cycle cancellation. Under nonzero
coefficient conditions, α weakly decreases along N and along reversed F.
It must therefore be constant along any directed mixed cycle. Such a cycle
has at least one nonempty N-segment immediately after a reversed F edge.
That F edge has equal-α endpoints, so its tail belongs to U_α; but the first
N-edge of the segment supports that same tail, a contradiction. Every map
coefficient vanishes. The earlier involution is a separate constructive proof.

The [mixed-closure companion](COMPONENT_MIXED_CLOSURE.md) gives a second
consequence: inserting a normal already implied by a mixed path preserves
every signed map coefficient. For an acyclic mixed order, the complete fiber
of normal selections realizing it is a Boolean interval, with the forward
Hasse edges mandatory. This supplies new semantic relations for regrouping.

## Strict corners and a component counting refinement

Now let F be a set of ordinary strict corners. At most one F edge has any
given tail. For every map with nonzero coefficient the only realizing subset
is

    J_α = {uv∈F : α(u)=α(v)}.

All other F edges must strictly increase α and are absent. Put

    T_α = {u : some uv∈F has α(u)=α(v)}.

The conditions above force U_α=T_α, so the coefficient is
(−1)^(|F|+|T_α|). This is uniqueness for EACH fixed map, not one surviving
map in the entire alternating sum.

Fix a complete component C and use F equal to all its strict corners S.
For any α, the coefficient of [α] in Σ_(A∈C) H(A\S,S) is therefore

    (−1)^(|S|+|T_α|) · m_C(α),

where m_C(α) counts the normal selections N=A\S satisfying:

- every selected normal edge weakly decreases α;
- no equal-α selected normal edge leaves a vertex of T_α;
- every nonroot outside T_α has an equal-α selected normal outgoing edge.

The preliminary map conditions and α(u)≤α(v) for every strict edge are
also required; otherwise m_C(α)=0. Equal-α strict tails are automatically
nonroots. The signs agree across all contributing N at this fixed map.
Applying [α]↦e_(fiber sizes of α) gives an exact formula for the relative HRV
sum. Different maps can have the same fiber-size partition, so this is not
a positivity assertion for its elementary coefficients.

On the coloring side, Σ_(A∈C) ∂_S K(A) is (−1)^|S| times the sum of the
mixed coloring enumerators: normals strict forward, corners weak reversed.
The missing theorem is equality with the displayed relative HRV sum after
commutative monomial evaluation. The counting refinement does not prove it,
nor does it show that any of these support sets forms an entire component.

## Two precise limits on a coloring-level proof

These diagnostics rule out overly strong matching requirements. They use the
same already-recorded four-vertex component, not substitute formalization goals.
Use one-based vertices, area (0,1,2,2), strict S={13,24}, and normal pairs
12,23,34. The complete ascent-one component is

    U=S+12  ↔  V=S+23  ↔  W=S+34.

### A fixed mixed-color fiber can be disconnected

Take vertex colors (2,4,1,3). Both strict corners satisfy the reversed weak
inequalities. Normals 12 and 34 strictly increase color, but 23 does not.
Thus the compatible fiber consists of the two isolated states U,W.
After deleting S these are different complete single-edge components.
Mixed acyclicity supplies neither connectivity of that fiber nor a unique
smaller-component owner.

For a local diamond with compatible common exterior, put
u=[c(a)<c(b)] and v=[c(b)<c(c)]. The fixed-color indicator defect is

    u+v−1−uv.

For a selected normal long ac, c(a)<c(c), so at least one short is allowed
and the defect is zero. For a reversed strict long ac, c(c)≤c(a), so both
shorts cannot be allowed and the defect equals

    −[c(c)≤c(b)≤c(a)].

If a common exterior constraint fails, all four terms and this correction
are zero. This identifies the precise local color correction. Its global
occurrences still need regrouping; no telescoping assertion is made.

### Canonical HRV chains cannot retain every vertex's color

Represent e_(fiber sizes) by colorings increasing in vertex order within
each HRV fiber. This is a valid enumeration of that elementary monomial.
For U,V,W the chain constraints are respectively

    1<2<4;        1<3 and 2<4;        1<2<3<4.

At the fixed color assignment (2,1,3,4), exactly V,W satisfy the original
selected-edge constraints, giving two occurrences. Only the middle canonical
HRV-chain constraints hold, giving one occurrence. Thus even the original
component equality cannot preserve every vertex's individual color through
this particular HRV-chain realization. A bijective approach must allow
redistribution of colors while preserving the commutative monomial, or use
a different realization of the elementary factors.

Primary checked this by hand and with the existing ordinary model, using
only three fixed recorded diagrams and permutations of their vertex colors.
External receipt `mixed-corner-residual/canonical_chain_color_probe.json`
under `/lake-cache/ai-projects/requests/VerticalStripLLT/` records the exact
states, chains and counts; SHA-256
`5dd8c65ffde88236e99e46589f62bdd840dff8ac1ca2cb5a1154684b5f7f04cb`.
No new graph enumerator, polynomial family or
Rust/Lean build was introduced. The Rust capability audit found no maintained
vertex-color-preserving component API; this was a bounded predicate check on
the existing model, not a replacement library.

## Residual diamonds and a reconstruction obstruction

Write R_X=∂_S X, for X=K or E. Let a<b<c, and fix exterior normal edges Q
avoiding the three triangle pairs. The two shorts are normal. If the retained
long ac is normal, include it in Q; its diamond remains an exact diamond
for R_X, because it holds separately for every deletion of strict corners.

If ac is strict, the full short state has R_X(Q+ab+bc)=0 by mixed-cycle
cancellation. Splitting the alternating sum according to retention of ac gives

    R_X(Q+ab)+R_X(Q+bc) = R_X(Q)+Φ_X(Q),

where

    Φ_X(Q) = Σ_(J⊆S\{ac}) (−1)^|(S\{ac})\J|
       · (X(Q+J+ab+bc)−X(Q+J+ab)−X(Q+J+bc)+X(Q+J)).

All states in Φ live in the genuine smaller diagram (G\{ac},S\{ac}) or
further deletions of its strict corners. The shorts remain NORMAL; they need
not be corners and cannot simply be declared strict. The smaller diagram
may be unsaturated, which the established corner branching handles.

This identity supplies a possible lower-normal-level term in the same diagram
and a smaller-area correction. To apply induction, their signed multiplicities
must be constant on complete components. Taking rational weighted sums of
corner-long flip pairs INSIDE the desired component does not always achieve
this, even in the already-proved forest family.

Here is the exact obstruction returned by Aristotle and audited by primary.
Use zero-based vertices, the complete four-vertex natural graph, strict 03,
and the eight-state tree component with normal pairs

    A={01,02}, B={02,12}, C={02,13}, D={01,23},
    E={12,23}, F={13,23}, G={12,13}, H={01,12}.

All eight states remain acyclic after reversing 03. The corner-long pairs
are exactly AC, DF, HG (long triangle 013) and AD, CF, BE (triangle 023).
Covering each state once by rational weighted pairs forces

    w(HG)=w(BE)=1,
    w(AC)=w(DF)=t,       w(AD)=w(CF)=1−t.

The lower-level multiplicities are constant on its whole components. But
in the corner-deletion diagram, area (0,1,2,2) with NO strict edges, the
three selected normal sets

    {01,02,13} ↔ {02,12,13} ↔ {02,13,23}

are actual flip neighbors, using retained longs 02 and 13 respectively.
The correction Φ has their multiplicities t, 0 and 1−t. Constancy would
require t=0=1−t, impossible over Q. Thus corner-long pairs from that source
component alone cannot provide the desired lower-diagram reconstruction.

This does not exclude normal-long diamonds, additional non-flip diamonds,
whole-component corrections, or the [chain normalization](COMPONENT_CHAIN_NORMALIZATION.md).
It rules out the uncorrected pairing scheme, not the component theorem.
Aristotle's other finite computational observations are not used as evidence
for a general statement. Its full return and request provenance are recorded
in [the consultation ledger](../ARISTOTLE.md).
