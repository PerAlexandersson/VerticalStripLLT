# Ordinary component expansion by diagrams and whole-component recurrences

2026-09-30. This note assembles the diagram proof. The new step is
[initial-vertex inheritance](COMPONENT_NN_REDISTRIBUTION.md#initial-vertex-inheritance-through-extra-edge-sectors),
which closes common-cover uniqueness for every natural graph without
articulation. Initial path prefixes and the proved right-attachment theorem
then supply the required component recurrences in arbitrary ordinary diagrams.
The final verification record is given below. No word-functional proof,
fundamental-basis calculation, or separate completed component theorem is an
input. This is a mathematical proof; no new Lean formalization is claimed.

The [cleanup audit and extracted lemmas](COMPONENT_DIAGRAM_AUDIT.md) give
a shorter area-sequence construction of the required prefix, explicit
interfaces for the sector and attachment arguments, and the proposed order
of formalization. Historical proof notes remain unchanged.

## The theorem

Let C be a complete flip component of an ordinary decorated natural diagram,
equivalently a non-circular Motzkin/Dyck-path diagram in the established model.
A state A is a selected forward relation containing the strict corners. Let
K(A;X) enumerate colorings strictly increasing along its selected edges, and
let lambda(A) be the partition formed by its highest-reachable-vertex fibre
sizes. Then, for every finite alphabet X,

    sum_(A in C) K(A;X) = sum_(A in C) e_(lambda(A))(X).   (1)

In particular the component is symmetric and elementary-positive. Its
coefficient at e_lambda is the number of states in C with HRV partition
lambda. Every flip preserves the number k(C) of selected normal edges.
Restoring the original shifted LLT weight therefore gives

    t^k(C) sum_(A in C) e_(lambda(A))(X),                 (2)

with nonnegative integer coefficients in t. We prove (1) before restoring
the shift, so marking a corner never introduces an unjustified division
or a comparison of different local powers of t.

## The new path induction

We recall the precise mechanism, to distinguish actual component paths from
an equality involving only prepared representatives.

Write M for all maximal natural corners. They form disjoint directed chains;
let r(v) be the terminal of v's chain. The established preparation P joins
any common-cover state to an anchor: M plus good normal edges uv with
r(u)<r(v). All anchors are subsets of one graph A*. Paths may temporarily
make other corners redundant, but retain every edge of M.

Suppose the first two corners are 0a,1b. Delete 0. The core G' loses exactly
0a and has no new maximal corner. All remaining chain terminals, and all
good core edges, are unchanged. An anchor consists of a core anchor, 0a,
and some extra edges 0v with 0<v<a and r(v)>r(a). Each such v has a corner
successor h_v>a. The proved crossing slide exchanges

    0v <-> a h_v, retaining 0a and v h_v,                (3)

and restores every other edge.

If the selected core is disconnected, choose an extra 0v joining 0 to a
core block different from the block of a. The matching a h_v is absent;
(3) joins the two core blocks. Repetition makes the core connected.
For a fixed set S of remaining extras, core paths lift unchanged: no
forward path between core vertices can visit 0. Thus core uniqueness
connects each fixed-S sector.

Let r be the core tree size and m its maximum good size. At total size s,
the nonempty connected-core sectors are exactly

    max(0,s-1-m) <= |S| <= min(|J|,s-1-r).               (4)

where J is the set of available extras. If deleting each matching core
edge a h_v from A*(G') leaves it connected, we can choose a core anchor
of any size r,...,m-1 omitting that edge. Equation (3) then connects
adjacent sectors. The subset band (4) is connected under these moves:
when an exchange would cross its lower bound, add the wanted element
before removing the unwanted one. A nontrivial one-level band cannot
occur, since removability implies m>=r+1. The empty-J case is immediate.
This proves initial-vertex inheritance.
The [forest-extension and subset-band lemmas](COMPONENT_DIAGRAM_AUDIT.md#two-finite-lemmas-for-the-sector-argument)
isolate the two elementary existence/connectivity facts used here.

Now use strong induction on vertex count for connected natural graphs
without articulation. Complete diagrams and graphs with at most two
corner chains are the previously proved bases. Write the first two
corners as 0a,bc, with 0<b<a<c. If b>1, the order-dual last-clique theorem
reduces to the smaller induced core {0,b,b+1,...,n-1}. If b=1, delete 0
and use the preceding sector argument. Both smaller graphs still have
no articulation: consecutive maximal cliques still overlap in at least
two vertices.

For the sector argument's removability hypothesis, contract the fixed
core corner chains. The proved quotient lemma gives a connected simple
graph without articulation. There are at least three quotient vertices
outside the base cases, so it has no bridge. Hence deleting any single
good edge copy leaves A*(G') connected. This verifies the hypothesis;
it is not an additional conjecture. Every induction call has fewer
vertices. We conclude:

**Common-cover uniqueness.** Every connected ordinary natural graph
without articulation has exactly one component containing connected
common-cover states of each feasible size.

An initial path can be added without changing this conclusion. Delete
its forced pendant vertices one at a time; core flips lift and every
removed vertex has just its one natural edge. This is only a path
argument. We do not equate component values under pendant contraction.

## Isolate one whole component in a layer

Let L be a connected source diagram with the preceding uniqueness property,
and let C be its connected common-cover component in edge layer s. Here s
counts ALL selected edges, including strict corners; it is unchanged by
remarking. It differs from the original normal-edge exponent k(C) in (2).
Some maximal corners may be unmarked, including the corner unmarked in the
DD/ND inheritance step, but C selects them all.

Every other component D in that source layer has an independently smaller
expression B_X(D), with identical integer coefficients for X=K,E:

- If D omits a maximal corner, delete that absent corner. Its image is
  one whole component with smaller natural area.
- If D is disconnected, reorder its weak blocks into consecutive intervals
  and discard the unused natural edges between them. This is one whole
  component in a smaller-area diagram.
- Otherwise D has no simultaneous-cover witness, by uniqueness. The proved
  alternating corner-deletion identity expresses it in whole components
  of diagrams with at least one natural corner deleted. Before applying
  that identity, mark every selected maximal corner strict, including any
  corner unmarked for DD/ND. Maximal-corner membership is constant on each
  component, so this is the same whole component and the same valuations,
  not an induction call.

These operations do not assume the expansion of any equally large unknown
component. In particular the alternating deletion uses a redundant-corner
witness at each state and the already proved closure of the deletion images;
it does not mistake a redundant edge at one state for an everywhere
redundant edge of the component.

Let F_j(R) denote the entire j-edge layer of the eligible NN or forward DN
target R, written as the union of its actual complete components. The
ordinary local diagram identities give

    NN: X(C)=X(F_s(R))+X(F_(s-1)(R))-sum_(D!=C) B_X(D),
    DN: X(C)=X(F_s(R))             -sum_(D!=C) B_X(D).   (5)

The same signs and integer multiplicities occur for K and E. All displayed
outputs, including the correction terms after expansion, are WHOLE
components. This completes the component collection: we add the explicit
extra source components to form a full layer, apply the diagram identity,
and subtract their independently smaller reductions.

Components with missing corners, disconnected selected relations, or no
common-cover witness reduce directly as above. There are no connected
states below the tree layer, and no common-cover states above |A*|.
Thus (5) handles every source layer, not just the tree or maximum layers.

All final NN diagrams have smaller natural area. The forward DN target
has the same area and smaller moment; its deletion corrections have
smaller area. DD and ND reduce to DN and NN by unmarking the obstructing
upper corner, keeping exactly the same selected-corner component. This
unmarking is a representation change, not an induction call.

## Articulations: use the first nontrivial block

It remains to provide (5) for a general connected ordinary natural graph,
where common-cover uniqueness at a fixed TOTAL edge count can be false.
We do not assume that stronger assertion.

We can choose the prefix directly from the area sequence. In a connected
ordinary diagram, an internal vertex v is an articulation exactly when
a_(v+1)=1. Indeed this equality excludes every edge crossing from below v
to above v. If instead a_(v+1)>=2, the edge (v-1)(v+1) bypasses v in the
adjacent-edge spanning path.

If every positive-index area is 1, the diagram is a path and is a base
case. Otherwise let j be the first index with a_j>=2, put b=j-2, and
let c>=j be the first index with c=n-1 or a_(c+1)=1. Then a_j=2.
The growth bound gives a_i<=i-b for i>=b+1. Thus the prefix on [0,c]
is an initial path to b followed by the block [b,c], whose internal cuts
all have area at least 2. This block has no articulation. The prefix
has common-cover uniqueness by the path induction, and [c,n-1] is an
arbitrary right attachment with no natural edge between the interiors.
See the [prefix lemma](COMPONENT_DIAGRAM_AUDIT.md#choose-the-prefix-directly-from-the-area-sequence)
for the endpoint and one-vertex-attachment cases.

Every flip belongs to one side of this cut. Its cover tests are internal,
since a forward path cannot leave a side and return. Thus any whole source
component factors as P*T, where P and T are whole components of the prefix
and attachment. For a connected common-cover component, P is connected
and has a common-cover witness.

Use (5) on P, retaining the color beta at c. All its local identities
preserve this right mark. For disconnected corrections put the weak block
containing c last, which fixes c and preserves its marked HRV fibre data.
The proved right-marked theorem therefore gives

    X(P)[beta]=sum_i m_i X(P_i)[beta],   X=K,E.          (6)

Only the marked equality (6) is needed for attachment; its derivation
does not enter the gluing argument. Glue the same T to every term.
Coloring sums glue at fixed beta, counting c once; exactly the HRV fibre
ending at c merges with the attachment's
fibre beginning at c. Whole-component factorization gives

    X(P*T)=sum_i m_i X(P_i*T),          X=K,E.           (7)

Every output is whole. No expansion for T is assumed. All prefix diagrams
have the same vertex set, so adjoining T adds the same vertices, area and
moment contribution to each term; every strict decrease is retained.

This also uses the required FIRST-DROP contact of the original source.
Our choice gives a_c>=2. If c<n-1, the next source area is 1; in the
prefix it is the appended 0. Both give a strict drop at c, and all
earlier comparisons coincide. If c=n-1, the prefix is the entire source.
Thus the source and prefix have exactly the same first strict drop.
The earlier DD/ND inheritance and contact-eligibility checks apply without
change. There is no uncontrolled left attachment: the initial path is
included in the prefix whose uniqueness was proved.

## Finish the elementary expansion

Use strong induction on

    (n, A, M),   A=sum_j a_j,   M=sum_j j*a_j,

ordered lexicographically, as in the proved coverage theorem. Normalize a
component to its saturated selected-edge envelope. A proper envelope already
reduces A; merely marking selected corners changes no relation or valuation.
Disjoint natural connected components factor over disjoint vertex sets and
have fewer vertices. A saturated path is the single increasing chain and
has K=E=e_n, including the one-vertex case; the empty diagram has value 1.

In the remaining connected case, direct smaller corrections apply unless
there is a connected common-cover component. The first-drop theorem chooses
an eligible NN/DN contact after the stated DD/ND unmarking. Use (5) if there
is no articulation, or (7) for the initial-path/first-block prefix and its
right attachment. Every final whole component is smaller in (n,A,M), with
the same coefficients for K and E. Induction gives K(C)=E(C). This proves
(1), and restoring the constant shift gives (2).

The full required NN/DN reassembly lemma is therefore proved. The construction
chooses the first-drop recurrence, which suffices for all ordinary components;
it does not claim that a raw local image is already closed under every target
flip. Signed source completion and the explicit smaller corrections perform
the missing collection.

## Dependency and verification record

The proof uses the following independently established diagram results:

- [Envelope normalization](FLIP_COMPONENT_INDUCTION.md), absent corners,
  and [alternating corner deletion](COMPONENT_CORNER_DIFFERENCES.md#a-signed-recurrence-in-whole-smaller-components).
- [Preparation](COMPONENT_NN_REDISTRIBUTION.md#normalize-entire-corner-chains-allowing-temporary-redundancy),
  [the chain quotient](COMPONENT_NN_REDISTRIBUTION.md#the-interval-graph-of-corner-chains),
  and [unrestricted crossing slides](COMPONENT_NN_REDISTRIBUTION.md#sweep-aside-the-obstructions-and-restore-them-after-the-slide).
- The complete-clique and terminal-clique path theorems and
  [last-clique inheritance](COMPONENT_NN_REDISTRIBUTION.md#extending-the-last-clique-from-a-connected-core).
- [Initial-vertex inheritance and its decreasing induction](COMPONENT_NN_REDISTRIBUTION.md#initial-vertex-inheritance-through-extra-edge-sectors).
- [First-drop coverage](COMPONENT_RECURRENCE_COVERAGE.md),
  [DD/ND inheritance](COMPONENT_DD_PACKETS.md#direct-one-component-inheritance-for-dd-and-nd),
  and [right-marked full-layer recurrences and attachments](COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#arbitrary-right-hand-attachments).

Related Rust: the existing external `dn_joint_span.rs` consumer reuses
Graph/Poset, the actual-flip model, crossing slides and the whole-component
correction audit. The four final modes are:

- `--ear-induction-structure`: all 6916 connected ordinary diagrams on
  3..10 vertices, including all 2055 without articulation. The decreasing
  branches are 8 complete cases, 618 initial-clique trims, 7 small-chain
  cases and 1422 initial-vertex cases. All 6908 non-path diagrams have the
  asserted first-nontrivial-block prefix and the same first drop as that
  prefix. The mode also replays 1308 crossing slides in 6238 actual flips,
  with up to four external extra edges and maximum path length 14.
- `--initial-ear-audit`: all 37 applicable diagrams through seven vertices,
  plus the fourth power of an eight-vertex path to test three extras.
  It checks 13474 connected source anchors, 1427 core joins (3944 flips),
  200 feasible sector bands, and 214 sector links (902 flips). Every core
  flip is compared with its lift: 344211 lifted states and 1420896 directed
  actual-flip incidences, including redundant-corner intermediate states.
  Core enumeration retains the existing 20000-state component guard.
- `--general-first-drop-layers --right-marked-layers`: all 41 feasible
  layers in seven fixtures, including genuine NN, DN, ND-to-NN and
  DD-to-DN contacts, newly covered three-/four-corner graphs and a two-edge
  initial path prefix. It checks 20274 survivor states, 2089 whole targets
  with 42054 states, 275 block corrections with 1943 states, 948 absent-
  corner corrections with 18051 states, and 287 alternating sources with
  1786 states. These give 6967 whole deletion terms, 5429 positive terms,
  4850 negative terms and 24358 redundancy witnesses. Every signed marked
  HRV identity, whole-output assertion and induction-order check passes.
- The same mode with `--prefix-only --right-marked-attachments` checks all
  six prefix layers after attaching the two-state triangle component to
  every term. All 3555 product-component checks pass, with 46844 product
  state visits and exact endpoint fibre data.

Frozen sources, commands, logs and hashes are retained in
`/lake-cache/ai-projects/requests/VerticalStripLLT/general-diagram-completion-20260930/`.
Final source-identical replays are recorded there. The maintained Rust
workspace is unchanged, and no Lean build, coloring enumeration or basis
calculation was used. The checks support the written general arguments;
finite enumeration alone is not used to assert unbounded uniqueness.
