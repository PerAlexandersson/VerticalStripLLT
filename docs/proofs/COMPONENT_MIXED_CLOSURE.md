# Mixed reachability preserves alternating state valuations

Status: proved mathematical statements, independently audited by primary and
Astra. These are not Lean declarations or a full component theorem. This
companion supplies additional exact relations for regrouping the smaller-area
corrections in [anchor slides](COMPONENT_ANCHOR_SLIDES.md).

## A normal edge implied by mixed reachability can be inserted

Fix a finite linearly ordered vertex set and disjoint sets N,F of forward
edges. No corner geometry is required. Define the mixed graph

    M(N,F) = N ∪ F^op.

Let H(N,F) be the full signed HRV-map sum from the
[coefficient theorem](COMPONENT_HRV_DIFFERENCES.md):

    H(N,F) = Σ_(J⊆F) (−1)^|F\J| [HRV(N∪J)].

Let K_F(N) be the analogous alternating strict-coloring enumerator, and let
E_F(N) be the image of H(N,F) under [α]↦e_(fiber sizes of α).

Suppose u<v, uv∉N∪F, and M(N,F) has a directed path u→v. Then

    H(N+uv,F)=H(N,F),
    K_F(N+uv)=K_F(N),       E_F(N+uv)=E_F(N).

Thus the HRV assertion holds before passing to elementary monomials. These
are unweighted state identities; adding a normal changes its ascent count.

For K, inclusion–exclusion gives (−1)^|F| times the enumerator with strict
inequalities along N and weak inequalities along reversed F. The witnessing
path contains a normal edge: a path using only reversed forward edges would
strictly decrease vertex labels, whereas u<v. It therefore already forces
c(u)<c(v), so inserting uv changes no coloring.

For H, fix a map α with nonzero coefficient before OR after insertion.
The exact coefficient theorem says that α weakly decreases along every old
normal and every reversed F edge. Hence α(u)≥α(v). If the inequality is
strict, inserting uv creates no equal-α outgoing support; all support
conditions and the coefficient sign are unchanged.

Suppose instead α(u)=α(v). Then every edge on the witnessing mixed path
has equal-α endpoints. If its first normal edge were preceded by a reversed
F edge, the last such reversed edge would arrive at a tail of an equal-α
F edge. Nonzero support requires that tail to have NO equal-α outgoing
normal. The next path edge, an OLD normal, contradicts this condition.
This argument applies equally when support is tested after insertion, since
every old normal remains present. Consequently the path starts with an old
normal out of u, and u already has equal-α outgoing support in N.

Inserting uv therefore leaves the unsupported set U_α unchanged, as well as
the N inequalities, the equal-F-tail conditions, and the requirement that
each unsupported tail have an equal-F successor. The coefficient
(−1)^(|F|+|U_α|) is unchanged. Starting from support on either side proves
that the supports agree as well, so every map coefficient agrees.

The argument does not assume mixed acyclicity. In the cyclic case the earlier
mixed-cycle cancellation also makes both sides zero. The theorem includes
ordinary transitive-edge redundancy and extends the previously proved
single-corner relative absorption.

## A closure operator and its exact acyclic fibers

Fix a set L of allowed forward normal edges, disjoint from F, and assume
N⊆L. Define

    cl_F(N) = {uv∈L : v is reachable from u in M(N,F)}.

This is extensive and monotone. Adding any of its edges adds only a shortcut
for an existing mixed path, so mixed reachability is unchanged. It follows
that cl_F is idempotent. Adding the finitely many missing edges one at a time
and applying the preceding theorem gives

    H(cl_F(N),F)=H(N,F),       K_F(cl_F(N))=K_F(N).

The same conclusion holds for E_F. Equality of closures determines the entire
mixed reachability relation, because M(N,F) and M(cl_F(N),F) have the same
reachability and the reversed F edges are fixed.

Now let C be a closed normal set whose mixed graph is acyclic. Let P be its
mixed reachability partial order and let B be its forward Hasse edges: pairs
u<v which are covers in P. Then B⊆C and the full closure fiber is exactly

    {N⊆L : cl_F(N)=C} = {N : B⊆N⊆C}.

Indeed, every realization of P must contain each of its Hasse edges directly;
a longer realizing path would supply an intermediate vertex. A forward Hasse
edge cannot be in F^op, so it must be in N. Conversely every backward Hasse
edge must already belong to F^op. Thus B∪F^op contains all the Hasse edges
of P and generates its entire order. Every B⊆N⊆C has exactly that order.

This is a Boolean interval of states on which both residual valuations, and
the full signed HRV-map sum, are constant. In particular deleting a normal
which is not a mixed-order cover preserves these valuations; all such normals
can be removed while retaining B and F^op. This operation preserves the mixed
order. It is different from strict-chain normalization, which preserves the
original flip component while generally changing the mixed order.

## Application to an overlapping correction packet

Let f=ac be strict, a<b<c<d, and let bd be a selected normal in the
exterior Q. Assume ab,bc,cd are absent from Q and are allowed normals.
The correction Φ_f^X(Q;ab,bc) in the anchor-slide note is the alternating
valuation with base Q and optional set

    F'=(S\{f})∪{ab,bc}.

This is an optional-difference set, not a declaration that ab and bc are
strict corners of a new diagram. In its mixed graph the path c→b→d uses
reversed bc and normal bd. The insertion theorem therefore gives

    Φ_f^X(Q;ab,bc)=Φ_f^X(Q+cd;ab,bc),       X=K,E.

Equivalently subtract the two bd-long diamonds with ab absent and present.
This moves the correction to an exterior with an additional normal. It does
not repair the boundary across bc↔cd when that is an actual target flip:
the original packet has
coefficients (−1,0) there, and the shifted packet has (0,1). Their difference
is still one. Another packet must supply the opposite boundary contribution.
The equality and its limitation hold with arbitrary common exterior.

## How this enlarges the permitted regrouping relations

For an actual component A of a fixed ordinary diagram, apply the closure with
L its normal edges and F its strict corners. Mixed-cyclic states contribute
zero. Grouping the rest by their closed sets gives, for X=K or E,

    Σ_(N∈A) X_F(N)
      = Σ_(acyclic closed C) m_A(C) X_F(B_C),

where m_A(C) is the number of component states in [B_C,C]. This is an exact
identity with the SAME multiplicities for both valuations. The component
has one fixed normal count, but there is no claim that its intersection is
the entire corresponding level of [B_C,C]. Binomial multiplicities cannot
be substituted without a separate component argument.

This limitation persists in saturated connected nonforest states. Reuse the
two-K4 articulation diagram, on one-based vertices, with areas
(0,1,2,3,1,2,3), strict corners F={14,47}, and normal sets

    B={12,23,45,56},       C=B∪{13,46}.

The mixed closure of B is exactly C and is acyclic. Its level of normal
cardinality five consists of B+13 and B+46. Every natural triangle lies in
one of the blocks [1,4] and [4,7], so every actual flip preserves the normal
count in each block. The two states have counts (3,2) and (2,3), respectively,
and hence lie in different ENTIRE components. Both selected graphs are
connected, contain a triangle, and have branching reachability posets. Thus
discarding only forests or pointwise chain cases does not fix level
connectivity. This does not rule out a refinement by the block counts.

More directly, each proved insertion supplies a common semantic zero relation
on signed states:

    Σ_(J⊆F) (−1)^|F\J|
       ([N+uv+J]−[N+J]).

Both K and E annihilate this relation. When the containing diagram has smaller
area, all its terms are legitimate smaller-area states. We may therefore add
integer combinations of these relations to a recurrence correction without
changing either semantic identity. They are available in addition to the
normal-long diamonds and the previously certified packet equations.

The remaining task is to use these freedoms to make the final signed
multiplicities constant on ENTIRE target components. Closure fibers are not
asserted to be components, their residuals need not satisfy K=E individually,
and equality of mixed orders does not justify erasing source-component labels.
No uniform solution of that reconstruction problem is claimed here.

The subsequent [ordinary component proof](COMPONENT_ORDINARY_PROOF.md)
resolves the theorem through a component-labeled word functional. It does
not require closure-fiber levels to reconstruct whole components.

The [labeled-poset continuation](COMPONENT_MIXED_POSET.md) also permits
redundant reversed edges to be removed, with an explicit sign change. It
gives a common incomparable-pair resolution and an exact total-order formula.

Related Lean: no declaration yet. This proof uses the audited coefficient
theorem rather than a new enumeration or compilation. The construction is
ordinary and uses finite forward HRV maps; no circular extension is asserted.
