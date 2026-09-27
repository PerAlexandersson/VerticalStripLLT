# Source branching: a companion without recomputing HRV

The component theorem remains unproved. Aristotle supplied this alternative
reduction; primary and Terra checked its mathematical content. It is not a
Lean result. The source identity below is the current cancellation target,
not an assumed theorem.

Use the strict/elementary convention and actual integer-cover HRV. For a
selected admissible orientation A, write B_A(r) for the fiber of sink r,
b_A(r)=|B_A(r)|, and s_A(r) for the number of GLOBAL selected sources in that
fiber. A source has no incoming selected edge, strict edges included. Put
E_A=product_r e_(b_A(r)). The target is K_C=E_C for each complete component C.
The [sink-branching note](COMPONENT_SINK_BRANCHING.md) proves that forgetting
strict decorations preserves entire components, so the full goal reduces
exactly to the undecorated case.

## Source deletion preserves the remaining HRV

Let S be a subset of the sources of A. A path starting at a retained vertex
cannot enter S. Thus its reachable set on the original integer cover is
unchanged by deletion. The increasing periodic compression of retained lifts
then sends its greatest reachable endpoint to the greatest reachable endpoint
in the smaller diagram. This identifies the new fibers with B_A(r)\S:

    E_(A\S) = product_r e_(|B_A(r)\S|),    with e_0=1.

Equal residue labels are understood through the compression map, not as a
literal equality between different finite vertex types. In particular this
argument retains winding information. An isolated vertex may be both source
and sink; deleting it removes its singleton fiber. The empty complement uses
the external empty-object convention with enumerator 1.

For fixed S, restrictions of orientations in C with S subset sources(A) have
constant multiplicity on COMPLETE components of the induced diagram. Fix
all selected edges incident to S. No path between retained vertices can enter
S, so every smaller flip lifts with precisely the same cover conditions and
the fixed boundary. A cycle cannot pass through a source. The reverse flip
is the inverse operation. Summing over boundary patterns proves constancy.
As with sink reconstruction, induced compression must identify edge instances
and their strict/normal status, not only vertex labels.

## The exact remaining identity

For 0<=s<=b define

    G(b,s) = sum_{j=0}^s binom(s,j) t^j e_(b-j).

For the positive fiber sizes used below, G(b,1)=e_b+t e_(b-1). The proposed
source companion is

    sum_{A in C} product_r G(b_A(r),s_A(r))
      = sum_{A in C} product_r G(b_A(r),1).                 (Src)

All quantities are read from A itself. There is no post-deletion search for
new roots. Both sides can be interpreted after evaluation in every finite
alphabet X, with t a separate new variable. A formal polynomial formulation
in the elementary generators is also possible; a Lean equivalence with all
evaluations would require the corresponding injectivity and degree bounds.

The identity is **unproved**. It is a global cancellation over a complete
component. It generally fails for individual orientations or local fragments.
The [leaf-packet note](COMPONENT_LEAF_PACKETS.md) proves a nontrivial packet
family and the coefficient of t^(n-1) for every complete component. The
remaining coefficients and a general packet decomposition are still open.
The [attached-chain note](COMPONENT_BRIDGE_PACKETS.md) proves another packet
family and isolates a marked-principal-ideal companion. It also shows why
packet cancellation without source-deletion closure cannot support induction.

## Why (Src) would close the proof

Adjoin a new SMALLEST color t. Strict colorings give the exact identity

    K_C(t,X) = sum_{A in C} sum_{S subset sources(A)}
                t^|S| K_(A\S)(X).

Assume the full theorem for smaller diagrams. For nonempty S, reconstruction
expresses each restriction sum as an integer combination of complete smaller
component sums; apply that induction hypothesis. Source deletion then gives
the left side of (Src). The S=empty term is handled by induction on the
alphabet size. The right side of (Src) is E_C(t,X), by elementary branching.
Both K_C and E_C vanish in the empty alphabet when n>0; the empty diagram
has value 1. This proves the full theorem if (Src) is established uniformly.

Conversely, given the smaller cases and the full component theorem at n, the
same coloring identity yields (Src) in every alphabet. Thus this route and
the cardinality-summed sink identity (S_k) are equivalent obligations under
the vertex induction. The fixed-subset sink identity (S_T) is stronger; no
necessity of that refinement is claimed. No symmetry of K_C is assumed in
the induction: t is always inserted as the first color.

## Compatibility with diamonds

The formal source-deletion operator

    D^src_k[A] = sum_{S subset sources(A), |S|=k} [A\S]

respects a four-state diamond, modulo smaller diamonds and cancellations.
The same proof works with a fixed deleted set S. For common long edge a->c
and optional shorts a->b,b->c, use [10]+[01]-[00]-[11].

- c cannot be deleted as a source, because a->c is selected.
- If b is deleted, only 00 and 01 can contribute. Their restrictions coincide
  after deletion of b, so they cancel.
- If a is deleted and b is retained, 10 cancels with 00, and 01 with 11.
- If neither a nor b is deleted, the remaining terms form the smaller diamond.

Source eligibility at every exterior vertex is unchanged across the four
states. This proves the local compatibility, but does not prove that its
global defect vanishes on every component.

## What cancellation must accomplish

The orientationwise defect is

    product_r G(b_A(r),s_A(r)) - product_r G(b_A(r),1).

If every fiber contains exactly one global source, this defect vanishes.
Source-free fibers and fibers with multiple sources supply opposite kinds of
correction. At coefficient t the desired cancellation is explicitly

    sum_{A in C} sum_r (s_A(r)-1) e_(b_A(r)-1)
                         * product_{q != r} e_(b_A(q)) = 0.

Setting every elementary generator to 1 shows that (Src) would imply equality
of the source-count and sink-count distributions on C. This necessary
condition alone is much weaker than the full fiber-size identity.

For a directed flip at a<b<c, the source count increases by
[indegree_A(b)=1], while the sink count decreases by [outdegree_A(b)=0].
Indeed, a retains its outgoing long edge, c retains its incoming long edge,
and only b can change either status. This degree calculation is valid both
ordinarily and circularly. It gives no componentwise cancellation by itself.

The next substantive target is a marked-source/marked-root transport or a
signed cancellation with an explicit rule preserving the FULL component
label. The root-only obstruction in the sink note still applies: exterior
flips must be available. Existence of a balanced flow must be proved, not
inserted as the hypothesis of a claimed solution.

## Critical forks: a normalization inside the actual component

The following mathematical lemma was proved independently by primary and
Astra. It is not yet a Lean declaration. Write alpha for the actual lifted
HRV potential and call a selected step u->v critical when alpha(u)=alpha(v).
Every selected step has alpha(u)>=alpha(v).

Suppose a<b<c<a+n and the selected lifted edges a->b and a->c are covers,
with alpha(a)=alpha(b)=alpha(c). Replace a->b by b->c, retaining a->c.
Then this is a valid circular flip and preserves alpha at EVERY lift.

Here are all the required checks.

1. The interval boundary makes b->c natural. Neither short edge can be a
   strict corner, by the corner lemma in the sink-branching note. The edge
   b->c is initially absent, since otherwise a->c would not be a cover.
2. A new projected cycle would use b->c. Its old return path from c would
   end at b+k*n for k>=1, implying alpha(c)>=alpha(b)+k*n. This contradicts
   the equal potentials. Thus the new selection is admissible.
3. An alternate lifted b-to-c path would be an old path, contradicting the
   old a->c cover. An alternate a-to-c path must use b->c, hence have an
   old a-to-b prefix avoiding the removed edge, contradicting its cover.
   The window has width less than n, so no other translate of b->c can occur.
4. The old alpha remains nonincreasing on all new edges, including b->c,
   so it bounds all new reachable endpoints. Conversely, an old maximum
   route using a->b can go instead through a->c and then to alpha(c).
   This reaches the same maximum: a vertex reaching a can reach alpha(a),
   and no continuation from a can exceed it. The maximum route from c
   cannot use the removed edge, by old projected acyclicity. Routes not
   using the removed edge remain intact. Periodic translates give the
   argument for every starting lift.

This yields a finite normalization without changing the diagram, component,
selected-edge count, or HRV potential. Fix the half-open interval (s-n,s]
of possible potential values. For each vertex residue v, choose its unique lift z_v
whose potential lies in that interval. Every critical edge connects these
canonical lifts in increasing order: its endpoints have equal potentials,
so they require the same period translation. A critical fork flip increases

    sum over selected edge orbits (canonical position of the head)

by z_c-z_b>0. There are finitely many selections. Therefore repeated critical
fork flips terminate. At termination, the critical reachability poset has
at most one outgoing cover at each vertex. Indeed, any two such covers
would supply another critical fork. A path between equal-potential lifts
has only critical steps, so a cover in this poset is also a full lifted cover.
Every non-root still has a route to its HRV root. Consequently each fiber's
critical Hasse diagram is a rooted tree, with exactly one outgoing cover
at each non-root. Redundant selected edges may still be present.

Two distinctions are essential. These are rooted TREES, not chains;
incoming forks remain. Also, a many-to-one normalization of orientations
does not preserve sums of K_A or reconstruct complete components with
constant multiplicity. A proof using this normalization must account for
its fibers.

In fact, confluence already fails in the ordinary complete diagram on five
vertices. Start from A={12,13,14,25,35,45}, with alpha(v)=5 for all vertices.
Flips 123 followed by 134 give

    T_1={14,23,34,25,35,45},    covers={14,23,34,45}.

Flips 134 followed by 124 instead give

    T_2={14,24,34,25,35,45},    covers={14,24,34,45}.

All four steps are critical outgoing-cover flips, and both final states
are terminal for this rewriting. Their coloring enumerators differ: T_1
has a chain 2<3<4<5 and no strict three-coloring, whereas T_2 has the
three-color enumerator x_1^3*x_2*x_3. Thus even with a single fixed HRV fiber,
this normalization cannot identify orientation contributions pointwise.
The two states do remain in the same full component, as required.

The equal-potential condition cannot be dropped circularly. In the full
circular diagram on four vertices, A={12,13,34,42} is projected acyclic.
Its edges 1->2 and 1->3 are lifted covers, but replacing 12 by 23 creates
the projected cycle 2->3->4->2. The old path 1->3->4->2 reaches the lift 6
of residue 2; thus alpha(1)=alpha(3)=6 whereas alpha(2)=2. This is precisely
the winding obstruction excluded in step 2.

## Conditional coefficient reduction

The final Aristotle return gives the following valid reduction, independently
checked by primary and Astra. Assume the full component theorem for every
smaller vertex count. Write the quasisymmetric coloring sum as
`K_C = sum_alpha c_alpha M_alpha`. Its coefficients depend on the ordered
positive color multiplicities alpha, independently of unused colors.

For k>0, the source restriction theorem makes `[t^k] K_C(t,X)` symmetric
in X: it is a sum of smaller complete-component enumerators. Therefore
`c_(k,beta)` is invariant under every permutation of beta. Sink restriction
likewise makes `c_(beta,k)` invariant under permutations of beta. For a
composition with at least three parts, permutations fixing the first position
and permutations fixing the last position generate all permutations. Hence
`c_alpha` depends only on the multiset of parts when alpha has length at least
three. The case k=n uses the empty-object convention.

This proves symmetry of those coefficients, not their equality with E_C.
One-part coefficients already agree: both models contribute x^n exactly for
the empty selected relation. The remaining obligations are:

- the two-part coefficients, including their symmetry;
- one source-defect coefficient per partition lambda of length at least
  three. If k is its smallest part, use the coefficient of
  `M_(lambda with one k removed)` in `[t^k](left(Src)-right(Src))`.

In particular, first-order source cancellation would settle every such
partition containing a part 1. It does not settle partitions without a 1.

There is also an unconditional support restriction. After forgetting strict
labels, let k be the constant selected-edge count of C. For a+b=n, if k>a*b,
both coefficients `[x_1^a x_2^b] K_C` and `[x_1^a x_2^b] E_C` vanish.
Indeed, a strict two-coloring permits only directed edges from its a-element
first color class to its b-element second class, at most a*b edge orbits.
The already proved aggregate HRV formula at coefficient q^k has nonnegative
terms; its zero coloring coefficient forces every individual HRV coefficient
in that degree to vanish as well. In particular the two-letter obligation is
automatic for k>floor(n^2/4). This does not isolate the surviving coefficients.

## Audit of the Claude local cancellation proposal

Claude Sonnet returned no general proof. A proposed pair-cancellation formula
omitted the exterior defect. The corrected local identity is useful for
checking future proposals, but does not prove (Src).

Consider a directed flip a->b becoming b->c, with long a->c retained,
where b initially has indegree 1 and outdegree 0. Its only incoming edge is
a->b. Put r=HRV(c), and let (B,S) be the size and source count of r's old
fiber. The old b-fiber is the singleton {b}: every other vertex reaching b
also reaches c via a, and therefore has a strictly greater reachable endpoint.
The flip changes only b's HRV and source status. Other vertices may lose
reachability to b, but their maximum is unchanged because they already reach
c. These statements also hold on the integer cover, by periodic translation.

Write H_j=e_j+t e_(j-1), d(B,S)=G(B,S)-H_B. Let L_rest and R_rest be the
source and target products, respectively, for the unchanged other fibers.
Pascal's rule gives

    G(B+1,S+1) = G(B+1,S) + t G(B,S).

The exact defect of the two-state sum is therefore

    L_rest * ((e_1+t)d(B,S) + d(B+1,S))
      + (L_rest-R_rest) * ((e_1+t)H_B + H_(B+1)).

The second line cannot be discarded. When S=1 the first line vanishes;
the exterior defect still remains. Only an independently established equality
L_rest=R_rest, or a proved cancellation after summing exterior states, removes
it. An unchanged exterior is not sufficient.

For a concrete certificate, take the flip {12,13}<->{13,23} and a fixed
disjoint exterior fork {45,46}, in the ordinary complete diagram on six
vertices. Here B=2,S=1, but

    L_rest=e_1 H_2,    R_rest=(e_1+t)H_2.

The pair defect is `-t H_2 ((e_1+t)H_2+H_3)`, which is nonzero. Summing the
ENTIRE exterior component would cancel it. Thus this is a counterexample
to the consultant's arbitrary-exterior pair claim, not to the component
conjecture. Primary and Astra checked the correction independently.

## Bounded Rust check of complete components

The external component probe reuses
`sym_poly_sym::llt::circular_highest_reachable_vertices`. It enumerates a
complete component from a supplied seed by BFS, checks both lifted cover
conditions and projected acyclicity for every flip, and expands (Src) in
formal elementary generators with checked integer arithmetic. Reaching the
state cap reports SKIP, never PASS. Strict decorations are forgotten using
the exact whole-component reduction, not by discarding selected constraints.

Primary reviewed Luna's build-free implementation, corrected an initially
reversed cover predicate and output/validation issues, and fixed two Rust
type annotations. Three focused tests passed, including a nonzero partial
component defect and a projected cycle invisible to the local cover test.
The Rust component masks and adjacency counts exactly matched the previous
enumerator on all 458 components, totaling 711 states, for areas
(0), (0,1,2,3), (3,3,3,3), and (2,2,2,2).

A deterministic sample then used n=5,...,8, ordinary complete diagrams,
complete circular diagrams, and constant circular area floor(n/2), at selected
edge counts n-1 and n+2. Seeds are acyclic with connected underlying graphs.
Of these 24 specified components, 21 completed and passed the FULL (Src)
identity; three exceeded the 20,000-state cap and remain inconclusive.
The completed components total 27,836 enumerated states; the largest has
10,646 states. No counterexample was found. This is evidence for the stated
inputs, not a proof for any general range.

Artifacts are external under `diamond-exploration/` in the existing request
directory. The source is `hrv-bridge/src/bin/component_source_probe.rs`,
SHA256 `ceb17c299e8698641acc171eed9cb924cf95d501f04b1aabc8bcffd21b8bb49e`.
The exact sample input metadata is `component-source-samples-input.json`,
SHA256 `5c48b2b8c9c1e71a1bbc48e9f50ff8a0902fb3b5e08a5e0e0d10d3383b3629df`.
Receipts are `component-source-tests.log`, `component-source-crosscheck.log`,
`component-source-samples.jsonl`, and `component-source-recheck.jsonl`.
The Rust checkout was at `d53fb193af3c69adedbd9ec8592f87235d809ffa`; its
actual `sym-poly/sym/src/llt.rs` SHA256 was
`c841d4281307ff27dede4288b51c5cec6edacc735691293b36ceb0ce04e4db29`.
No shared Rust source or new polynomial-family generator was introduced.
Maintained flip enumeration remains a separate integration proposal.

## Provenance

The inspected Aristotle snapshot is external at
`component-diamond-companion/active-snapshot.tar.gz`, with its mathematical
draft extracted to `returned-PROOF.md`. The draft explicitly says it has not
proved (Src), (S_k), or the full component theorem. Its remote compatibility
work is not integrated. Primary clarified compression labels, the empty
object, the evaluated/formal distinction, and the distinction between (S_k)
and (S_T). The terminal return is `final-result.tar.gz`, with mathematical
draft `final-PROOF.md`; the request ended COMPLETE_WITH_ERRORS.

The read-only Sonnet consultation finished successfully as a process, but
reported no proof. Its prompt, raw response and extracted `RESPONSE.md` are
external under `claude-source-companion/`. The extracted response SHA256 is
`d4664e67c13e01d55fe7aa486da1eb3988d9d01f11f889fd84877390c3159620`.
The corrected local identity above supersedes its unrestricted pair claim.
No local Lean build was needed for this research note.
