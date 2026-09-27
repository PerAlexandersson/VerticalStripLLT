# Endpoint recovery and separate ascent variables at articulation blocks

Status: proved mathematically from the already verified ordinary aggregate
HRV theorem. Primary and Astra independently checked the chain attachments,
triangular recovery, shared fibers, and boundary cases. These are not yet new
Lean declarations. No component expansion or connectivity conjecture is used.

This fills the semantic obligation exposed by the two-K4 counterexample in
[the active-corner note](COMPONENT_ACTIVE_CORNERS.md). The remaining ordinary
obligation is structural component isolation, now with separate block counts.

## The marked aggregate statement

Let D be an ordinary diagram on vertices 1,...,n, n>=1, with fixed strict
corners. Let A range over its selected orientations, k(A) its normal ascent
count, and K_A its strict order enumerator in X=(x1,...,xm).

Define F(A) to be the canonical chain forest: for each actual HRV fiber of A,
put its vertices in increasing vertex order and make them one strict chain.
The unmarked enumerator of F(A) is exactly the elementary monomial e_lambda(A).
This is an auxiliary selected relation, not a replacement definition of LLT.

For colors c,d, let K_A[c,d] restrict the coloring sum by f(1)=c and f(n)=d,
retaining the weight of every vertex. Define K_F(A)[c,d] in the same way.
The doubly marked AGGREGATE theorem is

    sum_A t^k(A) K_A[c,d] = sum_A t^k(A) K_F(A)[c,d].       (EP)

The single-mark versions follow by summing over the other color. No fixed
component is substituted for the complete orientation sum in this theorem.

## Strict chain attachments are valid diagrams

For r,s>=0, insert r new vertices before 1, with a strict adjacent chain
ending at 1, and s new vertices after n, with a strict adjacent chain starting
at n. These are the only new natural edges. The result is a valid ordinary
decorated diagram and adds no normal edges. Every old orientation extends
uniquely with exactly the same normal ascent count.

In area coordinates, suffix attachment appends s entries equal to 1.
For a nonempty prefix, put area 0 on its first new vertex, area 1 on its
remaining vertices, and area 1 on the shifted old first vertex. The other old
rows keep their areas. Originally the second old row has area at most 1,
so the last prefix edge is a corner. All new chain edges are corners and
every old strict corner remains a corner. The original one-vertex diagram
is included: prefix and suffix simply form one strict chain.

Only the fiber containing vertex 1 gains the r prefix vertices, and only
the fiber containing vertex n gains the s suffix vertices. If these are the
same fiber, its size increases by r+s. Indeed, every new prefix vertex reaches
exactly the old vertices reachable from 1; the old vertices reaching n are
exactly the old fiber of n, since n is the largest old vertex.

Consequently F of the enlarged orientation is obtained from F(A) by the SAME
prefix/suffix attachments. In F(A), vertex 1 starts its chain and vertex n
ends its chain. This observation handles both distinct and coincident fibers.

## Triangular recovery proves EP

Fix a finite alphabet of size m. For each r,s, the already proved aggregate
theorem on the enlarged diagram gives

    sum_(c,d) Delta[c,d] e_r(X_<c) e_s(X_>d) = 0,

where Delta[c,d] is the difference between the two sides of EP. The prefix
chain contributes e_r below the first color, and the suffix contributes e_s
above the last color. The preceding chain-forest observation gives these
same factors on the HRV side, not just an equality of unmarked partitions.

The equations for 0<=r,s<m force all Delta[c,d] to vanish over
Z[t,x1,...,xm]. For fixed s, start with r=m-1: only c=m can contribute, with
nonzero factor x1...x_(m-1). Cancel it in the polynomial integral domain.
Then r=m-2 isolates c=m-1 after the already known term has vanished; continue
down to c=1. This gives, for every c and s,

    sum_d Delta[c,d] e_s(X_>d) = 0.

Now s=m-1 isolates d=1 with factor x2...xm, and descending s successively
isolates d=2,...,m. Thus EP holds. No division or specialization of variables
is needed, only cancellation of explicitly nonzero monomials.

For m=0 there are no marked-color indices. The unmarked positive-degree
enumerators vanish. For n=1 the two marked vertices coincide, so both marked
sums are zero unless c=d, when they equal x_c. The chain-forest formulation
includes this case without a negative elementary index.

For reference, a fiber of size b containing only the marked minimum gives
x_c e_(b-1)(X_>c); one containing only the marked maximum gives
x_d e_(b-1)(X_<d). If distinct endpoints share a fiber, its factor is zero
unless c<d, and otherwise equals

    x_c x_d e_(b-2)(X_(c,d)).

The auxiliary identity for this last case is

    sum_(c<d) e_r(X_<c) x_c x_d e_(b-2)(X_(c,d)) e_s(X_>d)
      = e_(b+r+s)(X),

because c,d occupy positions r+1 and r+b in the chosen increasing list.

## Gluing at an extremal shared vertex

Let two ordinary diagrams occupy consecutive vertex intervals meeting only
at v, the maximum of the left interval and minimum of the right. Their union
is again a natural diagram. Orientations restrict independently to the two
diagrams; there are no natural edges joining their interiors.

Fix the color at v. Actual strict colorings then glue independently, counting
the weight x_(f(v)) once. Algebraically we can use the right coloring sum with
that vertex's weight omitted. Its equality with the corresponding chain-forest
sum follows from EP by cancelling their common nonzero factor x_(f(v)).

The left HRV fiber containing v and the right HRV fiber containing v merge;
all other fibers are unchanged. In the canonical chain forests, the left
chain ends at v and the right chain starts at v. Their union is precisely
the canonical chain on the merged fiber. Thus the same fixed-color gluing
operation applies to the chain-forest side. Summing the shared color proves
the unmarked formula, and retaining the two OUTER endpoint colors proves its
doubly marked version as well.

In elementary notation the unmarked merger of fibers of sizes p,q is

    sum_c x_c e_(p-1)(X_<c) e_(q-1)(X_>c) = e_(p+q-1)(X).

This proof uses the newly established pointed AGGREGATE identities. It does
not infer a pointed component identity from an unpointed component identity.

## Multivariate aggregate theorem

Suppose an ordinary diagram is a sequence of natural subdiagrams meeting
only at successive endpoint vertices. Assign a variable t_j to each block's
normal ascents. Repeated marked gluing proves the ACTUAL identity

    sum_A (product_j t_j^k_j(A)) K_A
      = sum_A (product_j t_j^k_j(A)) e_lambda(A).          (BG)

The analogous doubly marked identity also holds. The base case is EP, with
t renamed t_j; the gluing step just proved preserves the outer endpoint marks.
All these identities hold over integer multivariate polynomial rings and
for every finite alphabet, including the empty alphabet.

For a connected ordinary natural graph, its articulation blocks have exactly
this consecutive-interval form. Connectedness forces all adjacent edges.
An interior vertex v is an articulation precisely when no natural edge has
one endpoint strictly to each side of v. A crossing edge would connect the
two adjacent chains after deleting v, and conversely the absence of a crossing
edge separates them. Thus the maximal blocks meet successively at one endpoint.
Equivalently, a connected graph without an articulation has zero-based areas
a0=0, a1=1 and a_i>=2 for every i>=2: the smallest possible edge crossing
an interior vertex v is (v-1,v+1), and interval closure forces this edge
whenever any crossing edge exists.

Every flip lies in one such block: its retained long edge and its two shorts
belong to that block. Cover tests are internal, because a forward path cannot
leave a block and return. Complete components are Cartesian products of block
components and the vector (k_j) is constant on every complete component.

## The remaining structural companion

The corrected ordinary proposal is uniqueness of a connected active complete
component at each VECTOR (k_j) of block ascent counts. Equivalently, ask for
active uniqueness at fixed ascent in a natural diagram without an articulation.
This statement is still OPEN; BG does not prove it.

If it holds, the minimal-counterexample argument from the active-corner note
now uses coefficient extraction in BG. Corner splitting and always-redundant
corner deletion dispose of smaller-area components. Disconnected selected
components reduce to smaller vertex sets. At each block-count vector at most
one active connected component remains, so its defect is zero. This would
prove the full ordinary component theorem, and hence the balanced circular
case by the compatible-lift reduction. Unbalanced circular components remain
a separate obligation. No completion of either component theorem is claimed.

Related Lean: the aggregate input is
`coloringLLT_shifted_eq_orientation_sum` in `VerticalStripLLT/Expansion.lean`.
The proposed formalization modules are strict-chain extension, finite endpoint
recovery, and articulation gluing. Their implementation must retain the actual
coloring sum and actual HRV fibers; a scalar aggregate factorization at a shared
vertex is not a substitute for EP.

Luna's build-free API audit found no existing pendant constructor. The exact
word construction is `north diagonal^r U diagonal^s east` when the original
word is `north U east`. `PrefixScanners.lean` exports
`Step.endpointFrom_append`, `normalFrom_append`, and `strictFrom_append`;
`Concat.lean` supplies `validFrom_translate` and valid append lemmas.
`ElementaryColorings.increasingColoringSum_eq_esymm` is the existing strict-chain
enumeration bridge. Ordinary `SchroderPath.concat` and `OrientationConcatHRV`
concatenate DISJOINT vertex sets and do not implement this shared-endpoint
construction. Restricted-alphabet chain sums and nonzero variable products
are the remaining small algebraic APIs; no general symmetric-functions
library or division is required.
