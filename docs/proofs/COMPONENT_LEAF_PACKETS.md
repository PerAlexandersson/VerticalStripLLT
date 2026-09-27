# Movable leaf packets and star transport

We prove a family of source-companion cancellations and one coefficient for
every complete circular flip component. These are mathematical proofs checked
independently, not Lean declarations. The full component theorem remains open.
We use the notation G(b,s) and (Src) from
[the source-branching note](COMPONENT_SOURCE_BRANCHING.md).

## A binomial transport identity

We put H_b=e_b+t e_(b-1), so G(b,1)=H_b for b>=1. For integers
B>=0, 0<=S<=B and r>=0, and a commuting indeterminate x, we have

    sum_{k=0}^r binom(r,k) x^(r-k) G(B+k,S+k)
      = sum_{k=0}^r binom(r,k) (x+t)^(r-k) G(B+k,S).       (Leaf)

Indeed, Vandermonde's identity gives

    G(B+k,S+k) = sum_{q=0}^k binom(k,q) t^q G(B+k-q,S).

We substitute this, set l=k-q, and use
`binom(r,k)binom(k,q)=binom(r,l)binom(r-l,q)`. The inner sum is
`sum_q binom(r-l,q)x^(r-l-q)t^q=(x+t)^(r-l)`, proving (Leaf).
All calculations take place in the polynomial ring in t, x and the elementary
generators, with e_0=1. No component identity is assumed.

## A cancelling packet inside one complete component

We fix natural lifted vertices a<c<a+n and a set L of r vertices strictly
between them. We suppose a->c is natural. For each T subset L we select

    E_T = {a->c} union {a->b : b in L\T} union {b->c : b in T},

and no other edges. Vertices outside {a,c} union L are isolated. Monotonicity
of the interval boundary makes both short edges natural for each b in L.
The selected graph is a tree on these r+2 vertices. Thus its edges are
covers, and toggling a single b gives a valid flip on (a,b,c). All 2^r
states belong to the same complete component. This does not say they exhaust
that component. The toggles are independent, so they form a cube of states.

The same argument works with strict corners whenever these states are
admissible decorations: neither short edge can be a strict corner of a
triangle. Only the retained long edge can be strict. Alternatively we can
use the exact strict-forgetting reduction already proved in the sink note.

For k=|T|, the HRV fiber at c is {a,c} union T. It has size k+2 and k+1
global sources, namely a and T. Each vertex in L\T is a singleton HRV fiber
with no global source. The external isolated vertices are singleton fibers
with one source. These are actual integer-cover maxima, since every selected
path lies inside the arc from a to c, of length less than n.

Writing z for the number of external isolated vertices, the packet's two
source-companion expressions are therefore

    L_packet = H_1^z sum_k binom(r,k) e_1^(r-k) G(k+2,k+1),
    R_packet = H_1^z sum_k binom(r,k) H_1^(r-k) H_(k+2).

They agree by (Leaf) with B=2, S=1 and x=e_1. This proves the ENTIRE (Src)
identity for this packet, in every degree of t, while retaining its full
component label.

An arbitrary exterior cannot simply be factored out: its source and target
products can differ, as the audited Claude proposal showed. Likewise, when
S is not 1, (Leaf) retains G(B+k,S), which is not H_(B+k). An extension to
larger carriers must control both of these terms and the cover conditions.

## The next-to-leading coefficient for every complete component

We now prove, without assuming any smaller component identities, that for
every complete component C on n>=2 vertices,

    [t^(n-1)] sum_{A in C} product_r G(b_A(r),s_A(r))
      = [t^(n-1)] sum_{A in C} product_r H_(b_A(r)).       (Star)

For a nonempty selected relation A, the left coefficient is e_1 if A is an
incoming star together with isolated vertices, and is zero otherwise. To
see this, we need at least n-1 sources to reach t-degree n-1. There cannot
be n sources in a nonempty relation. Having exactly one nonsource forces
every selected edge to end at that vertex. All sources must be marked;
the sole remaining vertex gives e_1, with coefficient 1.

The right coefficient is e_1 if A is an outgoing star together with
isolates, and is zero otherwise. Each HRV fiber contributes at most one
power of t. A nonempty relation has at most n-1 fibers, so n-1 powers force
exactly n-1 sinks and exactly one nonsink. Every selected edge starts at
that vertex. If a is its center and c its greatest lifted child, its only
nonsingleton HRV fiber is {a,c}. Marking every fiber leaves e_1, once.

It remains to pair the two sorts of stars inside C. For an outgoing star
centered at a, let B be its nonisolated vertex set and let c be the
predecessor of a in the cyclic order on B: equivalently, c is its greatest
child lift in (a,a+n). The movable-leaf packet with L=B\{a,c} joins this
outgoing star to the incoming star centered at c. All these flips stay
inside the actual complete component; no reconstruction from a local window
is being assumed.

Conversely, given an incoming star centered at c, we take a to be the
successor of c in B, represented by the least incoming lift in (c-n,c).
The natural long edge a->c makes all reverse spokes natural. Reversing the
same packet joins it to the outgoing star centered at a. These assignments
are inverse, including a one-edge star. Thus the two star counts in C agree,
which proves (Star).

The empty selected relation is flip-isolated, and both expressions equal
(e_1+t)^n. This also handles n=1. In decorated diagrams the moved spokes
are normal: a strict a->b would contradict the later natural a->c, while
a strict b->c would contradict the earlier natural a->c. The retained
long edge and all original strict data are unchanged.

## What remains open

The packet identity proves a real cancellation, and (Star) isolates a
coefficient in every full component. Neither result supplies the missing
middle coefficients of (Src). The elementary packets above have tree
selected graphs; components with more selected edges already require a
larger class of packets. Even within tree components, other flips can leave
a packet, and packets can overlap. We still need a justified decomposition
with controlled multiplicities, or a larger transport that handles these
overlaps while preserving each complete component label.

Primary proved both statements. Terra independently checked (Star), including
normality and circular lift conventions; Astra independently checked (Leaf)
and the full packet cancellation. No Lean build was used for this note.
