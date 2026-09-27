# A labeled-poset valuation and its exact permutation formula

Status: mathematical proofs independently audited by primary and Astra, not
Lean declarations. This extends the [mixed-closure companion](COMPONENT_MIXED_CLOSURE.md).
The complete component theorem remains open; total mixed orders are not
individual equality cases.

## Redundant reversed edges and the normalized valuation

Retain the disjoint forward edge sets N,F and mixed graph M=N∪F^op.
Suppose u<v, uv∉N∪F, and M has a path v→u. Then

    H(N,F+uv)=−H(N,F),       K_(F+uv)(N)=−K_F(N).

For K, the weak inequality c(v)≤c(u) is already implied by the mixed path;
the extra inclusion–exclusion factor changes only the sign.

For H use the exact map coefficient theorem. A map α supported before OR
after insertion weakly decreases along the old path, so α(v)≥α(u). If the
inequality is strict, the new F edge is forced absent and contributes −1.
If equality holds, every edge on the path has equal-α endpoints. A reversed
F edge cannot be followed by a normal edge: its arrival vertex would both
lack and have equal-α normal support. The path therefore consists of a normal
prefix followed by a reversed-F suffix. That suffix is nonempty, since an
all-normal path cannot decrease the vertex label from v to u.

The last OLD reversed edge shows that u already has an equal-α outgoing
F edge and belongs to the unsupported set U_α. This holds when support is
tested on either side of the proposed insertion. Adding uv to F changes
neither U_α nor its support conditions, only the sign (−1)^|F|. Thus the
map supports agree and every coefficient changes sign.

Define normalized valuations

    J(N,F)=(−1)^|F| H(N,F),       Z(N,F)=(−1)^|F| K_F(N).

The preceding lemma and normal-edge absorption show that J and Z depend
only on the LABELED mixed reachability poset P when M is acyclic. To see this,
retain all its Hasse edges and remove every other mixed edge. Every removed
edge has a witness consisting of Hasse edges, so all removals are justified.
Forward Hasse edges go into N; reversed backward Hasse edges go into F.
This canonical representation depends only on P and the original vertex
labels. Write J(P), Z(P), and let j(P) be J(P) evaluated in elementary
monomials. No invariance under arbitrary relabeling is asserted.

## Resolving incomparable vertices

Let u<v be incomparable in P. Both orders obtained by adding u→v or v→u
are acyclic. We have, for V=J,Z, and consequently also V=j,

    V(P)=V(P+(u→v))+V(P+(v→u)).

On the Z side this partitions colorings by c(u)<c(v) versus c(v)≤c(u).
On the J side it is the exact alternating-sum identity

    H(N,F+uv)=H(N+uv,F)−H(N,F),

together with the normalization signs. Closure invariance makes the result
independent of the chosen edge presentation.

Iterating this resolution gives

    V(P)=Σ_(π∈LE(P)) V(P_π),

where P_π is the total mixed order whose vertex sequence is π. Each linear
extension occurs once: at any incomparable split it belongs to exactly one
of the two branches. The refinement terminates as comparabilities increase.
For Z, equal colors are ordered by DECREASING original vertex label, which
explains the strict/weak convention in this total-order refinement.

## Exact HRV formula for a total mixed order

Write π=π_1...π_n. In its Hasse representation, an ascent π_i<π_(i+1)
is a normal edge; a descent is a reversed F edge. Call a contiguous block
a mountain if its labels first strictly increase and then strictly decrease.
Either part may be empty, and singletons are allowed.

The full signed map J(P_π) has one term for each partition of π into
contiguous mountain blocks whose numeric maxima strictly decrease from
left to right. The map sends every vertex of a block to that block's maximum.
Its coefficient is

    (−1)^(the number of descents internal to the blocks).

Proof: a supported α weakly decreases along π. Its fibers are therefore
contiguous blocks with decreasing values; extensivity and idempotence force
each value to be the maximum label in its block. An internal descent followed
by an ascent would put an equal-F tail at an equal-N-supported vertex, which
the coefficient theorem excludes. Thus each block is a mountain.

Conversely, in a mountain block the vertices before the peak have equal-N
support. The vertices after the peak are precisely its unsupported tails,
each supplied by the preceding equal-F edge. The peak is a root. Across
block boundaries a normal edge merely decreases α, and an F edge increases
α and is forced absent. All support conditions hold, and |U_α| equals the
number of internal descents. Normalizing the coefficient sign gives the
displayed formula. Each resulting map determines its blocks uniquely.

After evaluation, writing j_π=j(P_π), this becomes

    j_π = Σ_(such mountain partitions B_1|...|B_k)
          (−1)^(internal descents) e_|B_1| ... e_|B_k|.

There is a short exact recurrence. Let r be the position of the global
maximum in π. If the prefix π_1...π_r is not strictly increasing, then
J(P_π)=0 even before evaluation: the first mountain block must contain that
maximum. Otherwise let s be the end of the decreasing run immediately after
position r, taking s=r if that run is empty. Then

    j_π = Σ_(ℓ=r,...,s) (−1)^(ℓ−r) e_ℓ j_(π_(ℓ+1)...π_n),
    j_empty = 1.

All choices of the first block appear exactly once. The suffix retains its
original label order; only block lengths index the elementary factors.

This formula is label-sensitive, not just descent-set-sensitive. For example
1324 and 1423 both have descent set {2}, but their values are respectively
0 and e_2²−e_3 e_1, directly by the recurrence. Their Z values are equal:
they impose the same sequence of strict and weak color inequalities. Hence
J cannot be recovered from that fundamental quasisymmetric enumerator alone.

## The component obligation after refinement

For a complete ordinary component A, let m_A(π) count its selected relations
N∪S which have π as a linear extension. Applying the common refinement to
each original forward selected relation gives the exact identities

    K(A)=Σ_π m_A(π) Z(P_π),
    E(A)=Σ_π m_A(π) j_π.

The SAME component-labeled multiplicities appear in both expressions. The
second expression now has the explicit mountain-block formula above. This
is a concrete permutation form of the remaining matching problem, not its
solution. In particular Z(P_π) need not equal j_π: the former is generally
nonsymmetric, whereas the latter is a signed elementary expression.

The next useful step would be a component-preserving redistribution of the
compatible permutations that matches the first-block recurrence. Such a map
must track the selected relation and its original complete component, as
well as the commutative color monomial. Aggregate identities or equality of
descent-set counts alone do not justify that redistribution. The existing
corner recurrences remain available for supplying smaller-area corrections.

Related Lean: no new declaration. The optional-edge and mountain-block
arguments were audited without enumeration or compilation. They use ordinary
finite forward HRV maps; a circular extension is not asserted.
