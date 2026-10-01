# Circular component proof: comparison with the Overleaf v9 draft

Status: complete mathematical proof for ALL circular flip components,
independently audited by primary and Astra. The component identity is now a
Lean theorem by the finite companion route; see
[the completion audit](../COMPONENT_COMPLETION.md). The polyhedral argument
below itself remains an audited prose proof.
The polyhedral argument comes from the Alexandersson--Dai Overleaf draft;
it was found during the user's requested comparison, not developed in this
Lean repository. No Overleaf file was edited.

Source: [Circular Vertical-Strip LLT Polynomials-v9.tex](</home/paxinum/Dropbox/Apps/Overleaf/LLT flip/Circular Vertical-Strip LLT Polynomials-v9.tex>),
SHA-256 `3b02859804569cf17a9fc037bd69390fc1afae2265cff559c752369ef05c9195`.
The bounded-face proof is at lines 1294--1638; compatible lifts at 1225--1274;
ordinary algebra and direct HRV extraction at 932--1199. The older `main.tex`
still contained incomplete recurrence sketches. This audit concerns v9.

## Comparison with the ordinary proof

The draft's relation [u_b,[u_a,u_c]]=0 is the negative of our four-word
relation, hence defines the same quotient. Its component functional uses the
same count of compatible states and the same actual-flip cancellation.
It works with weak enumerators and h; our finite coloring product uses strict
enumerators and e. Our descending-product factorization can be retained.

The draft supplies a shorter HRV extraction lemma. For a block B with maximum
r, expand its nested commutator as the sum, over T⊆B\{r}, of

    (−1)^|T| · inc(B\T) dec(T).

For an increasing selected graph, this word is compatible precisely when
every vertex of T is a sink of the induced graph on B. Summing signs gives
1 if r is that graph's unique sink, and 0 otherwise. For a set partition,
order blocks by decreasing maximum. The complete word contribution is 1
precisely when each block has its maximum as unique sink and every edge
between blocks goes toward a smaller block maximum. These are exactly the
HRV fibers. This proves extraction directly for every selected graph.

Thus the Lean plan can retain the existing finite strict/e factorization
and replace the longer mixed-poset semantic detour by this sink cancellation.
It does not need the draft's infinite symmetric-function stabilization, a
new general symmetric-functions library, or a finite-alphabet omega shortcut.

## The circular companion and its precise coefficients

By the existing universal-ambient lemma we may forget strict markings and
work in the complete circular natural diagram. Every original component
remains an ENTIRE component, with selected graphs and both contributions
unchanged. Let C be such a component, and let c(C) be its common number of
weak connected blocks.

For a selected DAG R, put

    P_R={z∈R^n : z_v−z_u ≥ ℓ(u,v) for every edge u→v∈R}.

Its lineality L_R consists of vectors constant on each weak block.
The quotient P_R/L_R is nonempty and pointed. For every face G bounded in
this quotient, retain its FULL tight edge set F, including redundant edges.
The following three facts are proved in the draft:

1. F admits compatible integer lifts. Tight equations have zero signed
   length around undirected cycles; choosing one root lift in each block
   makes all coordinates congruent to their original residues modulo n.
2. The affine tangent cone at G is P_F, and
   dim(G/L_R)=c(F)−c(R). Each tight set determines at most one face.
3. The same signed expansion holds for the strict coloring contribution J
   and the actual HRV elementary contribution E:

       W(R)=Σ_(bounded G) (−1)^(c(F)−c(R)) W(F),  W=J,E.

The last assertion is not assumed to hold for arbitrary graph functions.
Brianchon--Gram gives the indicator identity for P_R. Evaluating at z=n·f
proves the strict coloring assertion, since 0<ℓ<n. For HRV let d_R(u) be the
longest total natural length of a selected path from u. Then −d_R is the
greatest coordinatewise point of P_R∩R^n_(≤0): feasibility follows from the
longest-path recursion, and any feasible point is bounded above by following
paths to their endpoints.

Intersect the indicator identity with a compact box [b,0]. Its Euler
characteristic is 1 precisely when b≤−d_R, and 0 otherwise. This gives a
signed identity of those threshold indicators. Finite differences on the
integer vectors recover the identity of the EXACT vectors d_R, hence of
all lifted HRV maps u↦u+d_R(u). Elementary fiber evaluation proves (3).
The draft proves the required pointed version of Brianchon--Gram by capping
the polyhedron: terms from each unbounded face and its cap cancel in pairs.

## Why the coefficients belong to whole components

For a compatible-lift graph F define

    a_C(F)=Σ_(R∈C, G bounded modulo L_R, tight_R(G)=F)
                 (−1)^(c(F)−c(C)).

Suppose F and F' differ by the actual flip ab↔bc retaining ac, with lifted
vertices a<b<c<a+n. For every pair (R,G) contributing to a_C(F), both ab
and ac are tight. Their equations force bc tight as an equation, so bc
cannot already be an edge of R. Replace ab by bc in R to obtain R'.
Every point of G satisfies R', which proves its acyclicity: a directed cycle
would sum positive lengths to a nonpositive value.

A competing R-path between the displayed endpoints of ab or ac would have
total length equal to that edge's length. The sum of its nonnegative slacks
at a relative-interior point of G would be zero. Hence every edge on that
path would be tight, contradicting the cover condition in F. Thus the
source cover conditions lift from F to R. The equations on F and F' define
the same affine space, and the corresponding target face satisfies G'=G
as a subset of R^n. Its FULL tight set is F'. The same slack argument proves
the target covers. Therefore R↔R' is an actual flip in the ORIGINAL C.

The weak partition is preserved, so the quotient lineality is unchanged;
G'=G preserves boundedness and dimension. Reversing the short exchange is
the inverse construction. This proves a_C(F)=a_C(F') along every actual
flip. Consequently the signed expansion is a combination of ENTIRE balanced
components B, with identical integer coefficients for the two valuations:

    J(C)=Σ_B a_(C,B) J(B),       E(C)=Σ_B a_(C,B) E(B).

Compatible lifts identify every such B with an entire ordinary component.
The proved ordinary formula cancels each difference J(B)−E(B). This proves
the full circular theorem, including primitive unbalanced components.
Coefficients a_(C,B) can be negative; final positivity follows from the
original unsigned HRV expression, not positivity of this intermediate sum.

## Simpler finite recurrence for formalization

The user requested a readily formalizable replacement for the polyhedral
machinery. The [finite companion](COMPONENT_FINITE_COMPANION.md) now proves
the canonical coefficient identity and whole-component isolation. Its first
input is the following direct recurrence, checked by primary and Astra.

Let an undirected cycle in an acyclic selected graph R have nonzero signed
length. Choose its traversal so that its forward and backward edge sets P,N
satisfy Σ_P ℓ>Σ_N ℓ. Both are nonempty. Put B=R\N. For either actual valuation,

    Σ_(J⊆N) (−1)^|J| W(B∪J)=0.

For strict colorings satisfying B, at least one N-edge is also strict:
otherwise telescoping around the cycle contradicts the strict inequalities
on P. Toggle the least such optional edge to cancel signs.

For HRV fix a longest-length vector d occurring among the selections B∪J.
Every P-edge satisfies d_u−d_v≥ℓ(u,v). Telescoping and the signed length gap
force some e=u→v in N to satisfy d_u−d_v>ℓ(e). Choose the least such edge,
depending only on d. Adding it cannot increase any longest path, because d
is still a feasible upper bound; removing it cannot delete a maximizing
path, because every edge of such a path must have zero slack. Toggling e
therefore preserves the entire d vector and is an involution. It cancels
signs before any fiber evaluation.

Isolating J=N expresses W(R) as the same signed combination of proper
edge subsets on both sides. Edge count strictly decreases. Iterating stops
at graphs whose every undirected cycle has zero winding, hence at balanced
graphs. The finite companion proves the canonical terminal coefficients
by a separate recurrence, then groups them into complete balanced components.

There is a finite description of the draft's canonical coefficients. For a
balanced F⊆R choose compatible potentials p and contract the weak blocks
of F. Give each remaining directed edge gain

    δ_e=ℓ(e)−(p_head−p_tail).

F is the full tight set of a bounded quotient face exactly when every
directed cycle of this contracted multigraph has strictly negative gain
(including loops), and each weak block of R contracts to a strongly connected
graph. These conditions encode strict feasibility and absence of nonconstant
recession directions. The canonical sign is (−1)^(c(F)−c(R)). Strict feasibility itself needs no
linear programming: if the contraction has r vertices, replace each integral
gain δ by (r+1)δ+1. Every simple directed cycle has negative weight. Maximum
path weights from a new zero-weight source are finite (delete negative
cycles), and give integer offsets satisfying these scaled inequalities.
Dividing by r+1 gives the required strict block shifts. Conversely, summing
strict inequalities around a cycle forces negative total gain.

The finite proof of this coefficient identity is now complete: a signed sum
over ordered partitions removes the strong-connectivity condition, after which
a strict-slack optional edge gives an involution. The resulting coefficient
recurrence and edge-count induction prove the canonical expansion for both
valuations. The [companion note](COMPONENT_FINITE_COMPANION.md) contains the
full proof and the finite component-isolation argument.

### Deletion commutes with a disjoint flip

We can transport a cycle reduction term by term across an actual flip
ab↔bc retaining ac if its signed circuit lies in the common selected edges
and ac is not among the negative edges N. For every J⊆N, the graphs
(R\N)∪J and (R′\N)∪J differ by the same actual flip. All three required
local incidences remain. Deleting edges preserves covers; both children are
acyclic subgraphs of their respective parents. The circuit and its signed
length gap are unchanged, so the signs match as well.

This local commuting lemma does not yet give a reduction of a whole component.
A common usable circuit need not persist across all its flips. The remaining
overlaps use an exchanged short edge or put the retained long edge in N.
There the deletion can remove the flip witness, and changing the circuit
changes the child family. The complete finite companion handles these cases
through its canonical coefficient recurrence and componentwise coefficient
constancy; it does not require a direct matching of individual recursion
children across every overlapping flip.

## Verification boundary

The component identity is now Lean-verified by the finite companion route.
The bounded-face argument above remains an independent audited prose proof;
no general Brianchon–Gram or polyhedral Euler-characteristic formalization was
needed. Direct signed-sink extraction from the v9 argument is integrated in
`Components/WordProof/HRVScanExtraction.lean`.

Related Lean: `Components/WordProof/OrdinaryComponentExpansion.lean` and
`Components/WordProof/ComponentExpansion.lean` contain the complete ordinary and
circular strict/e identities by the word route (names ending in `_by_words`);
`Components/DiagramProof/Consequences.lean` and `CircularConsequences.lean`
prove the same statements by diagrams. See [the completion audit](../COMPONENT_COMPLETION.md)
for exact statements, model boundaries and checks.
