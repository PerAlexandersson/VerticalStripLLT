# Direct DN transport and its two five-vertex overlaps

2026-09-28. We apply DN to one component, retaining unmatched middle
terms in the corner-deletion diagram. We prove that the coefficients in
both output diagrams already agree across every flip except those in two
ordered five-vertex configurations. This is a reduction of the remaining
term matching, not a proof of the exceptional repairs.

We use the eligible ordinary DN geometry. We do not assume saturation,
source balance, connectedness, or a bound on the number of undirected cycles.
Throughout, X denotes either the unweighted strict coloring sum K or the
HRV elementary expression E. The same identities hold for both.

## The direct split

Let u<w<x<z, with x=w+1, and put

    e=uw,       f=wz,       q=wx,       r=xz,       e'=ux.

The source L has strict edges e,f and normal edges q,r. Its DN target R
has strict edges e',r and normal edges p=e,q. All other strict edges are
unchanged. Let Q include these common strict edges and a selection of the
common exterior normal edges. Write

    Lij(Q)=Q+e+f+i q+j r,
    Rij(Q)=Q+e'+r+i e+j q.

Here a bit zero omits its edge. Let h be an integer multiplicity constant
on complete source components, and put hij(Q)=h(Lij(Q)). For one component
C, take h to be its indicator. Let sigma exchange w,x on the entire
exterior selection, and set delta=h10-h01.

We also use the common deletion diagram H. Its natural graph is L-f=R-e',
and its strict set consists only of the unchanged strict edges. The pairs
e,r are unmarked natural corners in H. Put

    H10(Q)=Q+e+q,

so r is absent. Define target coefficients

    t00(Q)=(h00+h01)(sigma Q)-h01(Q),
    t10(Q)=t01(Q)=h01(Q),       t11(Q)=h11(Q).            (1)

**Direct transport identity.** For X=K and for X=E,

    X_L(h)=X_R(t)+sum_Q delta(Q) X_H(H10(Q)).             (2)

**Proof.** If f covers in L10(Q), then L10(Q),L01(Q) are joined by the
actual flip retaining f and exchanging q,r. Indeed, q is adjacent, and
a bypass of r would give a bypass of f through q. The one-endpoint cover
criterion supplies the reverse endpoint. Thus delta(Q) is zero whenever
f covers in L10(Q). Otherwise deleting f preserves the full reachability
relation, and hence both valuations. In all cases,

    delta(Q) X_L(L10(Q))=delta(Q) X_H(H10(Q)).            (3)

We pair the two middle states with coefficient h01(Q), leaving delta(Q)
copies of L10(Q). The source diamond gives

    sum_ij hij(Q) X_L(Lij(Q))
      =(h00+h01)(Q) X_L(L00(Q))
        +(h11+h01)(Q) X_L(L11(Q))
        +delta(Q) X_H(H10(Q)).                         (4)

The DN bottom identification sends L00(Q) to R00(sigma Q); the top
identification sends L11(Q) to R11(Q). We retain this distinction:
only the bottom identification relabels the exterior. Summing over Q
and applying the target diamond

    X_R(R10(Q))+X_R(R01(Q))=X_R(R00(Q))+X_R(R11(Q))

gives precisely (1)--(2).

The [general exposure lemma](COMPONENT_CORNER_EXPOSURE.md) gives a further
restriction on the unmatched coefficient delta. It vanishes whenever the
source 10 state has an actual neighbor exposing f, or has a path to such
an exposure which keeps q selected until the final step. This holds with
arbitrary exterior and without a cycle-rank assumption. It does not yet
handle paths that first leave q while f remains redundant.

These are the existing DN endpoint identities and ordinary diamonds, with
the unmatched term deleted directly. In particular, we need not enlarge C
to a balanced union of components. The older two-term deletion residual
can be replaced by the single term in (2).

## Flips which already carry through

Give H10(Q) coefficient delta(Q), and give every other H orientation
coefficient zero. We now check both output coefficient functions.

**Target.** Every target flip preserves t unless it retains e' or exchanges q.

For a flip preserving p,q in the full sector, the DN full-stratum closure
identification gives a source L11 flip, so h11 is unchanged. In either
middle sector, a flip not retaining e' lifts to L01 with the same exterior
exchange. Here is the complete argument:

- From R10, delete maximal e' and add maximal f. These operations do not
  change a cover test for any other natural edge, giving an L01 flip.
- From R01, add e. Only e' could acquire a bypass, and it is not tested
  by the flip. Pass from R11 to L11 using equality of transitive closures,
  then delete preserved adjacent q. This cannot remove the retained long
  or either exchanged short, and all their covers survive.

Consequently h01 agrees across both middle comparisons. The internal
R10(Q)<->R01(Q) comparison agrees directly by (1).

For a target 00 flip not retaining e', add p to obtain an R10 flip.
The only edge whose cover could change is e', since it is the only target
natural edge properly containing p. A new bypass would require a path
w->x, impossible without adjacent q. The middle lift therefore makes
h01(Q) constant along this 00 flip.

The DN bottom swap also sends it to a source 00 flip on sigma Q.
Adding r gives a source 01 flip: the only natural edge properly containing
r is f, and a new f-bypass would again need the absent q. Thus both h00
and h01 agree on the swapped exteriors, proving constancy of t00.

Finally, any flip changing p exchanges it with q and retains e'. Such a
flip is the already settled internal middle comparison. Every other flip
between sectors exchanges q. This proves the target assertion.

**Deletion diagram.** Every H flip preserving q preserves its coefficient.

The selected statuses of e,r are constant across H flips, because they
are natural corners. A q-preserving flip outside the sector e=1,r=0,q=1
therefore has coefficient zero at both endpoints. In that sector, add
maximal f to obtain an L10 flip, proving h10(Q)=h10(P).

Separately delete preserved adjacent q from the H flip and add f, giving
an L00 flip. Then add r to get an L01 flip, by the same q-absent argument
as above. Hence h01(Q)=h01(P), and delta is unchanged. This proves the
deletion assertion, without constraining the exterior paths or cycle rank.

## The 00 comparisons follow the 10 comparisons

For every actual flip between R00(Q) and R00(P), adding p gives an actual
flip between R10(Q) and R10(P), and

    t00(Q)-t00(P) = -(t10(Q)-t10(P)).                  (5)

Indeed, the DN bottom identification conjugates the original flip to a
source 00 flip on sigma Q,sigma P. It is an actual flip: the selected
relations are relabeled by exchanging adjacent w,x, and a flip staying in
00 cannot use both w,x in its triangle. Adding r to this source flip
preserves every tested cover. The only source natural edge properly
containing r is f; a new bypass of f using r would require the absent
adjacent edge q. Hence both h00 and h01 agree on sigma Q,sigma P.

Adding p to the original target flip also preserves every tested cover.
Only e' properly contains p, and a new bypass of e' would again require
q. Writing S=h00+h01, we therefore have S(sigma Q)=S(sigma P), while
the direct coefficients are t00=S composed with sigma-h01 and t10=h01.
This proves (5).

In particular, a left-hand flip retaining e' imposes just one condition
for its 00 and 10 versions: their coefficient differences have opposite
signs. Repairing its 10 comparison automatically repairs its 00 comparison.
No source balance or restriction on the exterior is used.

## The two ordered pictures

The preceding statements leave the following comparisons. A listed flip
is required only when it is actual in the full orientation.

| Vertex order | Diagram | Retained edge | Exchanged edges |
| --- | --- | --- | --- |
| u<t<w<x<z | R | ux | ut,tx |
| u<t<w<x<z | R or H | tx | tw,wx |
| u<w<x<t<z | R or H | wt | wx,xt |

For a flip retaining e'=ux, its third vertex satisfies u<t<x. The case
t=w is the automatic internal comparison; otherwise t<w because x=w+1.

A flip exchanging q has triangle twx or wxt. In the first case, the
left boundary at x is u in R and u+1 in H. Thus t>=u in R and t>u
in H. The case t=u in R is again the internal comparison, leaving
u<t<w<x<z. In the second case, the retained edge wt has t<z: maximality
of the original f excludes t>z, and f itself has been deleted in both
output diagrams. This leaves u<w<x<t<z.

The recurrence together with the exceptional flip therefore uses five
displayed vertices. Other vertices and all their selected edges remain in
Q; the table does not replace their cover conditions by those of an isolated
five-vertex graph.

## Remaining matching

Equation (2) starts from one component and has the same coefficients for
colorings and HRV. Its coefficients already agree on all unlisted flips in
both output diagrams. The remaining task is to use diamonds and redundant
edge identities in the two pictures to repair the target and deletion terms
together, preserving the settled comparisons. Once all flip comparisons
agree, the outputs are sums of whole smaller components.

The existing exact component data should be used to identify these repairs,
including their signs and multiplicities. A target repair is allowed to
change the deletion coefficients; holding the older residual fixed was an
unnecessary restriction and already has a recorded counterexample.

Primary and the existing independent Astra reviewer checked (2), every
flip lift, normality and the interval bounds. The argument uses neither
the completed component formula nor a finite enumeration as a proof.

The subsequent [joint-repair note](COMPONENT_DN_JOINT_REPAIRS.md) completes
both output diagrams for every component of the smallest right-hand
example and gives further diamond identities with arbitrary exteriors.
Their simultaneous use in the general diagram remains to be proved.

## A covering-anchor class of left retained-e-prime comparisons

2026-09-29. The new
[incoming-arm construction](COMPONENT_INCOMING_EDGE_TRANSFER.md#a-dn-left-overlap-consequence)
proves t10 constancy, and hence the corresponding t00 constancy by (5),
under the following arbitrary-exterior conditions. For the comparison
retaining ux and exchanging ut,tx, let A=L01(Q+ut). The source corners
e,f and the edge r must cover in A. After the actual source flip
ut -> tw [retain e], the resulting state must select a covering td
with x<d<z. The construction then gives an actual source path to
L01(Q+tx), without a cycle-rank or connectedness hypothesis.

At a saturated genuine first-drop DN contact, there is automatically a
strict corner with tail t and head d in that interval. Its cover after
inserting tw is an additional condition, not a consequence of strictness.
The same note also proves two further classes. If e,f,r,td cover initially
and w,x do not both reach d, an outgoing cut handles the initially
obstructing w-to-d paths. If instead e,td,wd,xd and ut cover, the four-flip
row xd->tx, ut->tw, tw->wx, wx->xd works even when both f,r are redundant.
Each construction proves the required source-component equality and hence
both t10/t00 comparisons, without adding a correction. The other cover
cases and global collection remain open, and the earlier independent audit
does not cover this new continuation.
