# Normalizing mixed-acyclic states along strict chains

Status: the terminal-chain lemma, ordered normalization, explicit endpoint
map and its fiber description are proved mathematical statements. Primary,
Astra and Terra independently audited the path and cover arguments. No Lean
formalization or full component-isolation theorem is claimed.

This continues the [corner-difference reduction](COMPONENT_CORNER_DIFFERENCES.md):
only states acyclic after reversing strict corners can contribute to a minimal
ordinary component defect. We give these states a fixed set of representatives
reachable by ACTUAL flips. The subsequent semantic matching remains open.

## Model and chain order

Let G be an ordinary natural graph, closed under subintervals, and let S be
any subset of its natural corners. Saturation is not required. A state is
A=N∪S with N⊆G\S. Let M(A) have normals N forward and all strict edges S
reversed. We assume M(A) is acyclic.

A corner has no properly containing natural interval. In particular at most
one strict edge has a given tail, and at most one has a given head. The
strict graph therefore partitions ALL vertices into increasing directed
chains, including singleton vertices with no incident strict edge. Write
r(v) for the largest vertex of v's strict chain and succ_S(v) for its strict
successor when it exists.

No normal edge joins two vertices of one strict chain. Consecutive vertices
are already joined by the strict edge. An edge joining nonconsecutive vertices
would properly CONTAIN a strict corner interval, contradicting maximality.
A normal edge v→y leaving a strict tail v satisfies

    v < y < succ_S(v).

If M(A) is acyclic, every strict edge is an ordinary reachability cover:
an alternate increasing path inside its interval could use no other strict
corner, hence would be a normal path closing a mixed cycle with its reversal.

## Terminal-chain elimination

Let B={u_0<...<u_k} be an ENTIRE strict chain. Suppose its terminal u_k has
no selected normal outgoing edge. Then A can be taken by actual flips,
all with mixed-acyclic endpoints, to a state with no normal edge leaving B.

Every normal exit u_i→y has u_i<y<u_(i+1). The head y is outside B and,
because these intervals are disjoint, at most one vertex of B can have a
natural normal edge to this y. Choose a reachability-minimal exit head y
in M(A): no DISTINCT selected normal exit head reaches y. Let its edge
be u_i→y.

After erasing this edge, there is no mixed path u_(i+1)→y. Such a path
would have to leave B; reversed strict edges cannot leave an entire strict
chain, so its first exit would be a different normal edge with head y'.
The suffix y'→y contradicts the choice. Adding y→u_(i+1) therefore cannot
create a mixed cycle.

This is an actual flip supported by strict u_i→u_(i+1). The long edge is
a cover by the preceding observation. An alternate forward path u_i→y
would lie inside the strict corner interval, use no strict edge, and give
the same forbidden path through a distinct exit head. Thus the short is a
cover too. The new short is natural and normal, being a proper subinterval
of the strict corner; it was absent, since otherwise M(A) already had the
cycle u_(i+1)→u_i→y→u_(i+1). The usual cover-flip criterion now applies.
Equivalently its target cover tests follow from the same path argument.

Each flip removes one selected normal exit from B and adds an edge entering
B. The number of exits decreases by one, so the procedure terminates.

## Ordered normalization of every strict chain

Process the strict-chain blocks by DECREASING maximum vertex. Maintain that
the UNION of previously processed blocks is absorbing for selected edges,
both in the ordinary graph A and in the mixed graph M(A). No selected edge
leaves that union for an unprocessed vertex.

Restrict to unprocessed vertices, retaining their order. Interval closure
survives order compression and all surviving strict edges remain corners.
New unmarked corners may appear, which is harmless: the terminal-chain lemma
does not require saturation. A path between unprocessed vertices cannot
enter the absorbing union and return, so cover tests in the restriction are
exactly the original cover tests for its edges.

The next block has terminal vertex larger than every remaining vertex outside
it. Thus its terminal has no outgoing normal in the restriction. Apply the
terminal-chain lemma there and lift its flips back to the original graph.
The absorbing property excludes new mixed cycles through processed vertices.
It also ensures that these are actual original flips. No flip changes an edge
of the previously processed blocks. Adjoining the new block preserves the
absorbing-union invariant.

A singleton block needs no flips: its vertex has no outgoing edge to the
unprocessed graph. Singleton blocks MUST be included, even when they lie
between the endpoints of another strict corner. Omitting them can leave a
terminal normal exit and invalidate the induction.

At termination, every selected normal edge v→y satisfies

    r(v) < r(y).

The final mixed graph has a fixed topological order depending only on S:
order the blocks by increasing maximum and order each block's vertices in
DECREASING original order. Thus every component containing a mixed-acyclic
state meets the compatible-state set of ONE fixed reference coloring.
This is an existence statement, not uniqueness of the component or reference
state, and not a claim that arbitrary fixed-color fibers are connected.

## The explicit endpoint map

Call a normal edge v→y an inversion when r(v)>r(y). Its tail has a strict
successor: otherwise r(v)=v<y≤r(y). Put h=succ_S(v); corner maximality gives
v<y<h. The ordered algorithm has the explicit endpoint P(A):

- keep every normal edge with increasing chain maxima;
- replace every inversion v→y by y→succ_S(v);
- retain all strict edges.

The replacement is a natural normal edge and has increasing chain maxima.
It cannot already be selected in a mixed-acyclic state, since together with
v→y and reversed h→v it would give a cycle. Two distinct inversion edges
have distinct replacements, because a strict head has a unique predecessor.
Thus normal cardinality is preserved.

Every step of ordered normalization makes exactly one of these replacements.
Previously processed blocks are untouched, and each newly inserted edge enters
a processed block. No increasing-maxima edge is ever removed. Consequently
its endpoint is independent of the choices within this algorithm, and its
path length is exactly the initial number of inversion edges. In particular,
P is idempotent, preserves the entire original flip component, and sends
mixed-acyclic states onto all states whose normals have increasing chain maxima.
Such states will be called anchors.

P is NOT constant on an entire component. For S={13,24}, the three-state
component with normals {12},{23},{34} has anchor images {12},{34},{34}.
Nor can we eliminate all normals leaving every strict tail: S={13,24},
N={12,34} is mixed-acyclic, but pushing 12→23 creates a mixed cycle.
The ordered construction permits normal edges entering earlier processed
blocks and does not assert that false stronger property.

## Exact fibers and their coloring sum

Fix an anchor with selected normals N_0. A selected anchor edge y→h is
rotatable if h has strict predecessor v with v<y<h. Its anchor condition
already ensures r(y)<r(h); the bare interval condition alone would not.
There are two possible preimages of this edge:

    keep y→h,       or select v→y instead.

Nonrotatable edges have only their original preimage. The full P-fiber is
EXACTLY the mixed-acyclic subset of this Boolean cube of choices. Distinct
pairs do not collide: good edges have increasing chain maxima and bad ones
have decreasing maxima, and the replacement map is injective.

Ordered normalization stays in the same P-fiber and reaches its anchor, so
every fiber is connected by actual flips. Two choices differing in one
coordinate, when both are mixed-acyclic, are joined by the strict-long flip
on v<y<h. The strict long is a forward cover; an alternate forward path
for the bad short v→y would be normal and would close a mixed cycle in
the good state. This verifies the short cover as well. The fiber is therefore
a connected induced subgraph of the coordinate cube for these corner flips;
it need not be the whole cube.

A complete source component's mixed-acyclic states consequently decompose into
WHOLE P-fibers, indexed by its anchors. This is genuine fiber reconstruction,
but it is not yet reconstruction into smaller-diagram components.

For a fixed coloring c obeying reversed weak inequalities on S, we have
c(h)≤c(v). In a rotatable coordinate, the two allowed conditions are

    c(y)<c(h),       or       c(v)<c(y).

They are disjoint. Thus a coloring selects exactly one coordinate choice when
c(y) lies outside the closed interval [c(h),c(v)], and none when it lies inside.
Impose also the usual strict inequalities on nonrotatable anchor normals.
Every choice satisfying these constraints is automatically mixed-acyclic:
a mixed cycle would contain a strict normal color increase and otherwise
weak increases, which is impossible.

Hence the sum of ∂_S K over a P-fiber equals (−1)^|S| times the enumerator
of colorings with weak reversed strict-chain inequalities, strict inequalities
on the fixed normals, and these outside-interval constraints at the rotatable
edges. There is no remaining orientation multiplicity at a fixed coloring.

This identity is only for K. A single fiber need not satisfy the matching E
identity. For S={13,24}, the anchor {12} has a singleton fiber. Its ∂_S E is
zero: its four deletion terms are e_(3,1)−e_(2,1,1)−e_(3,1)+e_(2,1,1).
Its ∂_S K is the nonzero mixed-coloring enumerator (for example colors
(2,4,1,3) satisfy it). Cancellation
must involve other anchors in the same component. The
[HRV difference formula](COMPONENT_HRV_DIFFERENCES.md) gives its exact other side.

## Strict-long flips between different anchors

There is a concrete local classification beyond fiber reconstruction. Let
an actual flip ab↔bc retain strict ac, with a<b<c, and suppose both endpoints
are mixed-acyclic. Let B contain a,c and C contain b.

If max B>max C, both shorts normalize to bc. This flip stays in one P-fiber.
If max B<max C, b has a strict successor d and corner maximality gives

    a < b < c < d.

Then P(ab)=ab and P(bc)=cd: the normalized endpoints exchange ab↔cd across
the crossing strict corners ac,bd. The normalized exterior is identical
because P acts edgewise. For S={13,24} this is precisely the slide 12↔34.

These anchors are connected by normalization paths and the original flip.
The [slide companion](COMPONENT_ANCHOR_SLIDES.md) now gives exact cover tests
for the apparent path ab→bc→cd with normalized exterior. It proves that the
path is always actual and mixed-acyclic for consecutive strict chains in
chain-max order, and derives its signed smaller-area correction for K and E.
Normal-long flips and general paths through mixed-cyclic states remain to
be controlled.
Astra supplied this endpoint classification; primary checked its successor,
normality and no-collision claims.

The next target is a recurrence for these anchor contributions, compatible
with the actual component relation and with both K and E. The normalization
has proved reachability, a deterministic endpoint, and whole fibers; it has
not proved the remaining semantic equality or component isolation.

## Images of a normal-long flip

Let an actual flip ab↔bc retain the NORMAL long ac, with a<b<c, and assume
both endpoints are mixed-acyclic. The vertices lie in three different strict
chains A,B,C: any pair in one chain would either be a strict edge or properly
contain one. Write Q for the exterior normals, Q'=P(Q), and h_A=succ_S(a),
h_B=succ_S(b) whenever required below. The exact normalized endpoint sets,
in addition to their common Q' and S, are:

| Order of chain maxima | Left, from ac+ab | Right, from ac+bc |
| --- | --- | --- |
| A<B<C | ac, ab | ac, bc |
| A<C<B | ac, ab | ac, ch_B |
| B<A<C | ac, bh_A | ac, bc |
| B<C<A | bh_A, ch_A | ch_A, bc |
| C<A<B | ch_A, ab | ch_A, ch_B |
| C<B<A | bh_A, ch_A | ch_A, ch_B |

Every required successor exists by the inversion criterion. When h_A is
used, normality of ac gives c<h_A; when h_B is used, c<h_B. Distinct chains
have distinct successors, and mixed acyclicity excludes collisions with
normalized exterior edges. The table follows directly by applying P to each
of the three local normal edges, including the retained long.

The normalized endpoints lie in the same complete component by the original
flip and the two normalization paths. Those paths may involve the exterior;
the table alone does not supply a bounded local path between anchors.

Even in the first row, and even with EVERY corner strict, the retained normal
long can cease to be a cover. Use zero-based vertices and areas
(0,1,2,3,4,4,5), with strict corners S={04,16}, and Q={02,45}. The two states

    S+Q+{23,25}  ↔  S+Q+{35,25}

are mixed-acyclic actual flip neighbors retaining 25: it and the exchanged
short are covers. The reversed strict edges are 4→0 and 6→1, neither of
which closes a cycle. Chain maxima at 2,3,5 have the first-row order.
Normalization replaces 02 by 24 and keeps every other displayed normal.
Both normalized states now have the bypass 2→4→5, so 25 is not a cover.
They are still anchors and hence mixed-acyclic. Thus saturation alone does
not supply the missing cover condition. This stronger diagnostic replaces
the earlier nonsaturated example.

Terra supplied the table and diagnostic; primary checked all replacements,
cover tests, natural corners and saturation. The separate
[mixed-closure companion](COMPONENT_MIXED_CLOSURE.md) concerns semantic
identities under mixed reachability and must not be confused with P or with
preservation of an actual flip's cover tests.
