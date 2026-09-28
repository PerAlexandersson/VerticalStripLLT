# Components for the square of an ordinary path

2026-09-28. This family provides terminal cases in arbitrary cycle rank
for the combinatorial component proof. Its component graph is explicit,
so the ordinary aggregate HRV identity isolates every component by edge
count. We do not use the general component theorem.

## Complete components

Let n≥3 and let G consist of the pairs ij with 1≤j−i≤2 on
0,...,n−1. Mark every maximal interval i(i+2) strict. The normal
edges are precisely i(i+1), indexed by i=0,...,n−2. We represent a
selection by the binary word recording these n−1 normal edges.

**Proposition.** For each 0≤k≤n−1, all selections with k normal edges
form one complete actual flip component Cₖ.

Every possible flip retains i(i+2) and exchanges i(i+1) with
(i+1)(i+2). If exactly one short edge is selected, both it and the
retained long are covers. Indeed, the only possible alternate directed
path inside [i,i+2] uses both short edges. Thus the actual flips are
exactly the replacements 10↔01 in consecutive positions of the word.

These moves connect all binary words with k ones: move the leftmost
one to the first position, then the next one to the second position,
and continue. No flip changes k. This proves both connectivity and the
whole-component assertion. In particular, |Cₖ|=binomial(n−1,k).

The strict edges form the two increasing parity chains. If k≥1, a
selected adjacent edge joins these chains, so the state is connected.
It has n−2+k selected edges and hence cycle rank k−1. For k=0 the
two parity chains remain separate.

## The HRV formula

Write h=⌊n/2⌋ and ℓ=⌈n/2⌉−1. Let e_j denote the elementary
symmetric polynomial in any fixed finite alphabet, with e₀=1.
We use binomial(a,b)=0 for b<0 or b>a.

**Corollary.** The strict-coloring sum of Cₖ is

    K(Cₖ) = E(Cₖ)
          = Σ_{s=0}^{h−1} binomial(n−2−s,k−1) e_{n−s} e_s
            + binomial(ℓ,k) e_{n−h} e_h.

First, the ordinary aggregate identity, in its normal-edge variable t,
is

    Σ_{k=0}^{n−1} t^k K(Cₖ) = Σ_{k=0}^{n−1} t^k E(Cₖ).

The preceding proposition shows that each coefficient is exactly one
complete component. Coefficient extraction therefore gives K(Cₖ)=E(Cₖ).
This uses only the ordinary aggregate theorem, whose proof is independent
of the component problem; see the
[aggregate extraction note](COMPONENT_CONNECTED_AGGREGATE.md).

We compute E(Cₖ) directly. The strict parity chains show that the only
possible highest reachable vertices are n−1 and n−2. Every vertex of
the parity of n−1 reaches n−1. A vertex of the other parity reaches
n−1 exactly when it can reach a selected adjacent edge i(i+1) with

    i ≡ n−2 (mod 2).

There are h such positions. Let s be the number of these positions
above the largest selected one, taking s=h if none is selected.
Exactly s vertices have highest reachable vertex n−2; all other
vertices have highest reachable vertex n−1. The HRV monomial is thus
e_{n−s}e_s.

For s<h, the largest selected position of this parity is fixed.
We exclude the s larger positions of that parity, include this one,
and choose k−1 further positions from n−2−s remaining positions.
This gives binomial(n−2−s,k−1) selections. When s=h, all k selected
positions belong to the other parity, giving binomial(ℓ,k) choices.
Summing proves the displayed formula. It also covers k=0 and the empty
alphabet without division or a separate symmetry assumption.

## Which components survive the mixed-cycle reduction

Reverse the strict edges and leave selected normal edges forward.
The mixed graph has steps −2 and +1. Two consecutive selected normal
positions give a directed triangle. Conversely, if no two selected
normal positions are consecutive, every +1 step in a directed walk
must be followed by a −2 step before the next +1 step. A closed walk
would then have strictly negative total displacement, which is impossible.
Thus the mixed graph is acyclic exactly when the binary word has no
consecutive ones.

Such a word with k ones exists exactly when k≤⌈(n−1)/2⌉=h. Hence
Cₖ survives precisely for 0≤k≤h. The connected surviving components
have ranks k−1, so this gives terminal cases of arbitrarily large rank.
For k>h, the already-proved mixed-cycle correction also applies, but is
not needed for the direct coefficient argument above.

## Why leftmost NN does not supply every step

For n≥4 the area sequence is (0,1,2,...,2), and the corner incident
to 0 is 02. Its leftmost NN terminal-gap condition would require

    area(3) < area(2),       that is, 2<2.

It therefore fails. The incoming-boundary equality at 0,1 does hold;
it is not the failed hypothesis. Reversing the vertex order gives the
same diagram, and the natural graph has no articulation: after deleting
any vertex, consecutive surviving labels differ by at most two.

For n≥5, the eligible DD contact is at the terminal triple

    (n−5,n−3),       (n−4,n−2),       (n−3,n−1).

The final area drops from 2 to 0 at the ordinary cut. The initial
triple 02,13,24 is terminal only when n=5; for larger n its last
column does not have the required strict area drop.

Thus leftmost NN eligibility does not follow merely from reversal and
absence of articulation. This is a limitation of that coverage argument,
not an unresolved family: the proposition already solves these components.
A complete recurrence proof still needs to handle diagrams outside such
terminal cases, including the remaining DN/DD and higher-rank joins.

## Verification and scope

Primary and the existing Astra reviewer checked the component description,
coefficient extraction and local recurrence hypotheses. Exact actual-flip
enumeration also checks every Cₖ for 3≤n≤12, with the expected binomial
component sizes. The theorem is uniform in n; the finite check is supporting
evidence only. No new polynomial sequence was generated computationally.

Related Rust: external `adjacent_transfer_general.rs`, mode `--square`,
using the existing complete-component model. Frozen source and receipts:
`/lake-cache/ai-projects/requests/VerticalStripLLT/adjacent-transfer/`.
No Lean or manuscript change is claimed.
