# A sink-deletion companion for the component formula

This is proof research, not a Lean theorem or a completed component proof.
We give a reconstruction argument and an exact remaining combinatorial
identity. Unlike fixed-diagram straightening, this route reduces the number
of vertices. It applies to the circular model if the proposed companion is
proved with actual lifted HRV values.

Throughout this note we use the strict/elementary convention. For a selected
acyclic relation A, put

    K_A(X) = sum over strictly order-preserving colorings of A,
    E_A(X) = product over HRV fibers B of e_|B|(X).

For a complete flip component C, sum these expressions over A in C. The
target is K_C=E_C. The letter E here avoids confusing this expression with
the weak/complete-basis expression H in the earlier diamond notes.

## Strict decorations can be forgotten without splitting components

The full component theorem reduces to the undecorated case S=empty. This is
an exact component identification, not a slicing hypothesis.

On the integer cover write b(v) for the first incoming neighbor of v. A
corner u->v satisfies u=b(v) and b(v+1)>u. It cannot be the left short edge
in a natural triangle u<v<w<u+n: monotonicity gives b(w)>u, excluding the
required long edge u->w. It cannot be the right short edge in a triangle
a<u<v<a+n: naturalness of a->v would require b(v)<=a<u=b(v). The argument
works for every periodic translate.

Only short edges are toggled by a flip. Consequently the selected status of
EVERY natural corner is constant throughout each undecorated flip component.
For a diagram with strict corner set S, the map

    A -> S union A

from its normal selections to undecorated selections preserves the entire
selected relation. Its image on any complete decorated component is an ENTIRE
undecorated component: every flip there avoids S, and removing S gives the
inverse flip. Admissibility, integer lifted paths, cover tests, strict-order
enumerators and actual HRV fibers are identical. Ascent counts differ by the
constant |S|, which does not affect the unweighted component identity.

Thus proving the component formula for all undecorated circular diagrams is
equivalent to proving it with all permitted strict decorations. Primary and
Astra independently checked the geometry. This reduction does not prove
diamond-to-chain normalization in the undecorated case; that remains a
separate substantive issue. In particular, cover-flip diamonds are only a
subset of the available selected-long valuation identities.

## Reconstruction after deleting sinks

Fix a subset T of the vertex set. Restrict attention to orientations A in C
for which every vertex in T is a sink of the selected relation (strict edges
included). Let D\T be the induced diagram, with inherited cyclic order.

**Reconstruction lemma.** The multiplicity

    m_(C,T)(eta) = #{A in C : T subset sinks(A), A restricted outside T = eta}

is constant on every complete flip component of D\T.

Here is the proof. Fix a selected boundary pattern on all edges incident to T.
Since T consists of sinks, no selected directed path between two retained
vertices can pass through T. Thus both reachability and the lifted cover test
between retained vertices agree with those of the restriction. Any flip in
the smaller diagram lifts to a global flip while retaining the boundary
pattern. It still has T as sinks. A new directed cycle could not pass through
T, and would therefore already be a cycle in the smaller orientation.

This operation stays inside C and is reversed by the reverse smaller flip.
It is consequently a bijection between the two extension sets, for EACH fixed
boundary pattern. Summing over boundary patterns and then following a path
of smaller flips proves the claim. The sink stratum need not be a union of
whole global components; that is not used.

The required geometric closure is stated in the manuscript as
`lem:circ-induced-restriction`. If the retained lifts are u_j, cyclic rank
compression sends u_j to j. It preserves induced edge instances, natural
directions, strict corners, directed paths and translation by a period.
Hence a smaller flip triple lifts to a triple in one original period. The
empty complement is treated as the empty diagram separately, since the
current circular area type requires positive size. A one-vertex complement
has no edges.

This is a mathematical proof of reconstruction, not yet a Lean implementation.
In particular an implementation must supply the edge-instance equivalence;
an informal identification of compressed vertex labels is insufficient.

## The remaining companion identity

Every projected sink r is the HRV of itself, and hence labels one nonempty
fiber B_A(r). For fixed T, consider the stronger proposed identity

    sum_{A in C, T subset sinks(A)} E_(A\T)(X)
      = sum_{A in C, T subset sinks(A)}
          product_{r in sinks(A)} e_(|B_A(r)| - [r in T])(X).       (S_T)

We use e_0=1. This is NOT proved. Either side retains the complete source
component label C. It permits different orientations to exchange terms;
there is no assertion that the two contributions of one A agree.

For the component theorem, the weaker statement obtained by summing (S_T)
over all T of each fixed cardinality k suffices:

    [t^k] E_C(X+t)
      = sum_{A in C} sum_{T subset sinks(A), |T|=k} E_(A\T)(X).   (S_k)

Here X+t means appending one variable, not shifting each existing variable.
The equality e_d(X+t)=e_d(X)+t e_(d-1)(X) explains the right notion of
fiber removal. It does NOT itself prove (S_T) or (S_k): after a sink is
deleted, the remaining vertices can acquire different highest reachable
vertices. The corresponding assertion using complete homogeneous functions
would have different branching terms and is not intended here.

## Why this would prove the full theorem

A strictly order-preserving coloring using a new largest color can give
that color precisely to a subset T of the sinks. Its remaining colors form
a strict coloring of A\T. Therefore, without any conjectural assumption,

    K_C(X+t) = sum_{A in C} sum_{T subset sinks(A)}
                t^|T| K_(A\T)(X).

Induct on the number n of vertices. For nonempty T, reconstruction expresses
the corresponding sum of K_(A\T) as a nonnegative integer combination of
complete smaller component sums. The induction hypothesis replaces each by
its independently defined E expression. If (S_k) holds for k>0, this gives

    K_C(X+t) - K_C(X) = E_C(X+t) - E_C(X).

Induction on the alphabet size now proves K_C=E_C in every finite alphabet:
at alphabet size zero both vanish when n>0. The empty-diagram case is 1.
No prior symmetry of K_C, no circular no-wrap reduction, and no identification
of components by coarse invariants is needed. This is an implication with
the explicit unproved premise (S_k), not a proof by renaming the conjecture.

## Compatibility with diamonds

There is a further proved local fact. On formal selected-graph sums, the
sink-deletion operator

    D_k[A] = sum_{T subset sinks(A), |T|=k} [A\T]

respects four-state diamonds, modulo diamonds on smaller vertex sets. The
same assertion holds for a fixed T.

Write the common long edge as a->c and the two optional shorts as a->b and
b->c. The relation is [10]+[01]-[00]-[11]. The vertex a is never a sink.
If b is deleted, only states 00 and 10 can contribute; their restrictions
are identical and cancel. If c is deleted and b is retained, states 10 and
11 have identical restrictions, as do 00 and 01. If neither is deleted,
deleting exterior sinks leaves the same diamond. The case deleting both
b and c is already included in the first cancellation. This proves the
claim, including arbitrary exterior edges and circular lifts.

Thus diamonds are compatible with the desired induction. However, the
auxiliary swaps from `DIAMOND_STRAIGHTENING_AUDIT.md` require a stronger audit
after deletion: fixing the original sinks does not fix newly exposed roots.
For example, let

    R = {13,23,24,35,45},    R' = (3 4) R.

Both are naturally increasing relations with unique sink 5, so both have
E=e_5. After deleting 5 their HRV partitions are respectively (2,2) and
(3,1). A sink-fixing conjugacy alone is therefore insufficient for this
companion. A useful generalized diamond proof must preserve deletion data
or account for its correction explicitly.

## A winding-sensitive auxiliary structure

For an admissible periodic relation, let alpha(z) be the greatest reachable
integer lift. Along every selected step z->w,

    alpha(z) >= alpha(w).

Call an edge critical when equality holds. Every nonsink has a critical
outgoing edge, since a path to alpha(z) starts with one. Keeping all critical
edges preserves every actual HRV. Choosing one critical successor per
nonsink gives a projected rooted forest whose components are exactly the
actual HRV fibers.

Critical natural edges also have no hidden winding alternatives. For
z->w with 0<w-z<n, a projected alternative path lifts to w+kn with k>=0.
If k>0, it reaches alpha(w)+kn>alpha(z), a contradiction. Thus it ends at
w, and monotonicity forces every edge of the path to be critical. Projected
and lifted cover tests consequently agree for a critical natural edge.

This forest is an auxiliary structure, not a component invariant. Deleting
noncritical edges changes the coloring constraints in general. A prospective
sink-promotion proof must transport those constraints rather than discard them.

## Why a finite ordering of sinks is insufficient

In the full circular graph on four vertices with no strict edges, take

    A={13,21,24},    B={13,21,41}.

These form a complete two-state flip component, using lifts (2,4,5).
In A, the path 2->5->7 reaches the lift of 3 farther than the direct edge
2->4. Its actual HRV fibers are {1,2,3} and {4}; B has one fiber. Thus the
actual sum is e_(3,1)+e_4. Selecting the largest reachable sink by its finite
label instead gives e_(2,2)+e_4. Even after component summation, replacing
lifted HRV by finite sink priority changes the target.

## Evidence and next step

A first bounded audit checked (S_T) for every T and every component in four diagrams:
ordinary area (0,1,2,2) with strict 13,24; full circular area (3,3,3,3);
circular area (2,2,2,2); and ordinary area (0,1,2,3), the last three with no
strict edges. All passed. This is evidence only, not a proof or a larger-range
claim. A subsequent bounded audit checked all 449 decorated circular diagrams
of size four, including empty admissible sets; all passed. The size-five
diagram in the locality obstruction below also passed for COMPLETE global
components. These checks do not prove any uniform statement.
The audits reused the Rust library's actual
`sym_poly_sym::llt::circular_highest_reachable_vertices`; Python only
orchestrated the existing finite flip enumerator and compared multiplicities.
External scripts and receipts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/`.

The next proof target is a component-preserving sink-promotion bijection or
a diamond argument for (S_k), possibly proving the stronger (S_T). Its local
operations must retain the source component and handle the change of roots
after deletion. Reconstruction and finite checks cannot replace this step.

## Partial ordinary sink promotion

There is a concrete promotion step for the largest ordinary vertex n. List
its selected cover predecessors as u_1<...<u_d. Rotate the incoming forks
from right to left: replace u_j->n by u_(j-1)->u_j, keeping u_(j-1)->n,
for j=d,d-1,...,2. These are reverse flips within the same component.

The cover conditions justify each move. After removing u_j->n, there is no
remaining path from u_j to n; otherwise that edge was not a cover. Adding
u_(j-1)->u_j therefore leaves u_(j-1)->n a cover, and the new edge is a cover
because a pre-existing alternative path would have contradicted the old
cover u_(j-1)->n. Later steps add edges into, not out of, earlier predecessors.
Interval closure supplies each new short edge. The removed edge cannot be
strict because a smaller incoming natural edge exists; the new short cannot
be strict and already selected, since that would contradict the original
two-cover configuration.

Suppose additionally that n-1 belongs to the original ancestor set B of n.
Then u_d=n-1. Every vertex in B\{n} reaches an original cover predecessor
without passing through n, and that path survives the rotations. The new
chain through the predecessors makes it reach n-1 after n is deleted. No
vertex outside B can enter B, and every added edge lies inside B. Thus the
resulting restriction has exactly the old HRV fibers with the fiber of n
shrunk by one vertex.

This establishes existence of a suitable same-component target in this case.
It does not establish a bijection or equal multiplicities, and it does not
handle the case n-1 lies outside B. Those are essential remaining obligations
for turning this promotion step into (S_T).

## Ordinary reduction to a largest-sink promotion

There is a useful reduction if a suitable general largest-sink promotion is
found. For an arbitrary ordinary sink s, set

    V_s(A) = {v : HRV_A(v) <= s}.

This set is successor-closed and contains s as its largest vertex. Selected
paths within it cannot exit it, so all induced flips lift globally. Every
outside vertex has a route to its original root, greater than s, wholly
outside V_s(A): a route entering this successor-closed set could not reach
that root. Internal changes therefore leave exterior HRVs exactly unchanged.
The active set is consequently recoverable after any internal flips.

Thus a bijective largest-sink promotion can be applied on this induced set
without losing invertibility through its A-dependence. If it matches the
post-deletion HRV partition, it also preserves the fibers of all larger marked
sinks. Processing a fixed marked set increasingly would then give the full
ordinary (S_T). This remains conditional on the largest-sink promotion theorem.
No such bijection has been proved.

Circularly, using canonical representatives does not directly supply the same
reduction. Choose z_v maximal in its residue class with alpha(z_v)<=s. Then
alpha(z_v) lies in (s-n,s], but selected steps can end at z_w-kn for k>0.
Replacing this endpoint by z_w can create a false route to a higher root.
Two paths with the same projected endpoints can also have different winding;
projected acyclicity does not rule this out. A circular proof must retain these
period shifts. The critical forest alone cannot remove the extra constraints.

## A descending sweep is insufficient

For the largest ordinary sink n, each valid cover flip on (a,b,n), extended
by the identity where no flip is available, is an involution. Their product
is therefore a permutation of every full component. A candidate used the
order of decreasing a, then decreasing b. Its desired HRV matching is false.

In the complete ordinary diagram on four vertices, with no strict edges, take

    A={12,13,14,23}.

Its HRV fibers are {1,4} and {2,3}, so shrinking the 4-fiber gives (2,1).
The sweep's only move replaces 12 by 24. Deleting 4 afterwards leaves
13,23, whose HRV partition is (3). The earlier triangle 134 was blocked by
the path 123; the later flip removes that obstruction. Invertibility of a
fixed sweep does not establish the partition identity.

Luna supplied the external bounded probe. Primary corrected its specification
through review before running it; the corrected code checks involutivity and
component membership and uses the Rust HRV API. It stopped at this size-four
counterexample. There is no claimed size-five pass for the sweep.

## Root-containing flips alone are insufficient

A stronger obstruction excludes EVERY promotion confined to flips containing
the marked largest sink, regardless of order or revisiting.

Take ordinary area (0,1,2,3,2), with no strict edges, and set

    E={13,14,24},    F=E+34+35,    T=E+35+45.

The only natural edges into 5 are 35,45, so the only flip triangle containing
5 is 345. The states F,T form its full two-state orbit, with the required
cover conditions. Their HRV data are:

| State | Original fibers | Shrink the 5-fiber | Delete 5 |
| --- | --- | --- | --- |
| F | 135 / 24 | (2,2) | (4) |
| T | 12345 | (4) | (3,1) |

Thus this restricted orbit has deletion sum e_4+e_(3,1), whereas its shrunk
fiber sum is e_4+e_(2,2). No permutation inside that orbit can match them.

At T the exterior flip on 134 is valid: 13 and 14 are covers, and replacing
13 by 34 gives another orientation in the FULL component. Hence the example
does not refute (S_T); it proves that the full component is essential. A
successful promotion or generalized diamond argument must move the exterior
data, as anticipated in the original component sketches.

Primary derived this obstruction by hand and checked the four HRV maps with
the Rust API; Astra independently checked the diagram and cover conditions.

## Exact defect data, including circular winding

The missing cancellation can be expressed using the deleted diagram and its
incoming edges. This is an orientationwise identity, unlike the conjectural
component cancellation.

First take the ordinary largest sink n, put B=A\{n}, and let I be its selected
incoming neighbors, including strict edges. Set

    U = union_{i in I} {v : v reaches i in B}.

Then the old n-fiber is U union {n}. If F_r denotes the HRV fiber of r in B,
every vertex outside U retains its B-HRV, so the deletion defect is exactly

    delta_n(A) = product_r e_|F_r|
                   - e_|U| product_r e_|F_r\U|.

In terms of f_r=|F_r| and u_r=|F_r intersect U|, this is

    product_r e_(f_r) - e_(sum_r u_r) product_r e_(f_r-u_r).

Here is the circular version for ANY fixed sink subset T. Put B=A\T, but
perform comparisons on the ORIGINAL integer cover. For a retained lift v,
let beta(v) be its greatest endpoint reachable within B. For each t in T,
let R_t(v), when it exists, be the greatest reachable lift of t. Such a path
consists of a B-path followed by one incoming edge to t. A path cannot pass
through a removed sink, so

    alpha_A(v) = max(beta(v), all defined R_t(v)).

These candidates never tie: they end in distinct residues, with beta ending
at a retained vertex. Let U_t consist of the retained residues for which
R_t is the largest candidate. The definition is invariant under translating
v by a period, since every candidate increases by the same period. Put
U=union_t U_t. Then

    shrink_T(E_A) = product_{t in T} e_|U_t|
                     * product_{r outside T} e_|F_r(B)\U|,

and the exact defect is E_B minus this expression. Products include empty
fibers with e_0=1. A newly exposed B sink which was not an A sink has empty
residual fiber automatically.

Monotone compression of retained lifts transports beta and its fibers to the
actual HRV data of the smaller diagram. It must NOT be applied to a removed
sink when comparing beta and R_t. Missing R_t is an absent value (or minus
infinity), never an arbitrary integer sentinel. If B is empty, all U_t are
empty and the external empty-object convention makes both expressions 1.

Primary and Terra derived the ordinary formula; primary derived the circular
extension and Astra independently verified it. It gives explicit data for a
possible signed cancellation or flip-graph flow. It does not show that the
defects sum to zero over a component, which remains the central open step.
