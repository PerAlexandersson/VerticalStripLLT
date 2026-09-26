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

## Provenance

The inspected Aristotle snapshot is external at
`component-diamond-companion/active-snapshot.tar.gz`, with its mathematical
draft extracted to `returned-PROOF.md`. The draft explicitly says it has not
proved (Src), (S_k), or the full component theorem. Its remote compatibility
work is not integrated. Primary clarified compression labels, the empty
object, the evaluated/formal distinction, and the distinction between (S_k)
and (S_T). No local Lean build was needed for this research note.
