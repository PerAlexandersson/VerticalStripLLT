# Diagram proof: cleanup audit and lemmas for formalization

2026-09-30. We audit the mathematical proof at `8ccde0e`, before its new
Lean formalization. The [assembled proof](COMPONENT_DIAGRAM_COMPLETION.md)
remains the main entry point. The lemmas below are proved on paper, not new
Lean declarations. We use the same diagram paths and whole components;
the separate word-functional expansion is not an input.

## Decisions from this round

We found no gap in the reviewed completion argument. We make two implicit
points explicit: alternating deletion first re-marks every selected maximal
corner, and full layers count total selected edges rather than selected
normal edges. Both operations were already justified in the source notes.

We replace the general block decomposition used to select a prefix by the
area test below. We extract the finite facts underlying the sector proof
and the one-mark attachment interface. These changes shorten the future
formal proof without changing the recurrence or its signed corrections.

The primary reviewed initial-vertex inheritance, preparation, the chain
quotient, crossing slides and last-clique inheritance. The independent
Astra reviewer `diagram_audit` reviewed component isolation, deletion
corrections, attachment, first-drop selection and induction order, and
checked the proposed area-prefix replacement. Its conclusion was that the
reviewed argument has no mathematical gap. This fulfills the project
guide's independent review of the proposed decomposition. It is not a
kernel check or a claim to have reverified every historical auxiliary proof.

## Two finite lemmas for the sector argument

**Forest extension at every size.** Let H be a connected finite undirected
graph on q>=1 vertices, and let F be a spanning forest with F subset E(H)
(isolated vertices allowed). For every q-1<=t<=|E(H)| there is a connected
spanning edge set of size t containing F.

We extend F to a spanning tree: while there are two components, connectedness
of H supplies an edge joining different components. Each addition decreases
the number of components by one and creates no cycle. The resulting tree
has q-1 edges. Add arbitrary remaining edges to reach t.

In particular, if d is not required and H-d is connected, the same argument
gives every size q-1,...,|E(H)|-1 while omitting d. In initial-vertex
inheritance, H=A*(G'), F=M', and d=a h_v. Thus (IV3) supplies exactly the
witness needed for each sector transition; a separate spanning-tree choice
for each cardinality is unnecessary. All these edge sets are anchors,
since they contain M' and use only good normal edges.

**Subset-band connectivity.** Let J be a finite set of size p. Join subsets
by inserting or deleting one element. For 0<=L<=U<=p, the subsets with
L<=|S|<=U form a connected graph if L<U, or if L=U is 0 or p.

If L<U, remove elements until size L. Two distinct L-subsets can exchange
an unwanted element for a wanted one by first adding the wanted element
and then deleting the unwanted one; these moves use sizes L+1 and L.
Each exchange decreases their symmetric difference. Thus all L-subsets
connect, and reversing the initial removals reaches every allowed subset.
At L=U=0 or p there is just one subset. For 0<L=U<p there are multiple
subsets and no edges, so this exception must not be omitted.

For (IV4), write s for the total source size, r for the core tree size,
and m for its maximum size. Feasibility means that there is a t with

    r<=t<=m,       t+1+|S|=s.                         (A1)

Equivalently, with integer subtraction, L=max(0,s-1-m) and
U=min(p,s-1-r). We consider only a nonempty band. If p>0, removability
gives m>=r+1. Were 0<L=U<p, neither bound would be truncated, and L=U
would force m=r. Thus only the connected cases occur. If p=0, there is
one feasible sector. For Lean, (A1) avoids accidental truncated natural
subtraction and also handles empty layers explicitly.

These two lemmas are the only abstract connectivity facts needed for
initial-vertex inheritance. We still prove the diagram-specific facts:
preparation reaches an anchor; crossing slides connect it to an anchor
with connected core; each fixed-S core path lifts; a crossing slide links
the neighboring sectors. Intermediate states may have redundant corners.
Only the representatives at the ends need be anchors.

## Choose the prefix directly from the area sequence

Let a_0,...,a_(n-1) be a connected ordinary area sequence, so a_0=0,
1<=a_i<=i for i>0, and a_(i+1)<=a_i+1. Its natural edges are
(u,i) with i-a_i<=u<i. The boundaries i-a_i are nondecreasing.

**Articulation test.** For 1<=v<=n-2, vertex v is an articulation if and
only if a_(v+1)=1.

If a_(v+1)=1, its boundary is v and all later boundaries are at least v.
No edge joins a vertex below v to a vertex above v. Removing v therefore
separates two nonempty sets. Conversely, if a_(v+1)>=2, the natural edge
(v-1,v+1) is present. All adjacent edges are present by connectedness.
Their spanning path, with v bypassed by this edge, connects every other
vertex after v is removed. Removing an endpoint also leaves a connected
adjacent-edge path. These statements include all needed small cases.

**First nontrivial prefix.** Suppose some a_j>=2. Take the least such j,
put b=j-2, and let c>=j be least with c=n-1 or a_(c+1)=1. Then:

- The induced prefix on [0,c] is the initial path [0,b] followed by a
  connected graph on [b,c] without articulation.
- The original graph is that prefix and its right attachment [c,n-1],
  with no natural edge joining the two interiors.
- The prefix and original graph have the same first strict area drop,
  using appended terminal area zero.

We have j>=2, a_(j-1)=1, and a_j=2 by the growth bound. All earlier
positive-index areas are 1. Starting from a_(b+1)=1, the same bound gives
a_i<=i-b for every i>=b+1. Hence every edge with head above b has tail
at least b: the earlier portion attaches only through b. The graph on
[b,c] has initial areas 0,1 and all subsequent areas at least 2. The
articulation test proves that it has no articulation. It contains the
triangle at b,b+1,b+2, so it is nontrivial.

If c<n-1, the equality a_(c+1)=1 and monotonicity of the boundaries
exclude all natural edges from below c to above c. If c=n-1, the right
attachment is the one-vertex component at c. In both cases a_c>=2.
Earlier comparisons of consecutive areas are identical in prefix and
source. At c, the prefix compares with zero; the source compares with
1 if there is a proper attachment and with zero otherwise. Both are
strict drops. Their first strict drops therefore agree.

If no a_j>=2 exists, the graph is already a path. This proof supplies
exactly the prefix needed by the recurrence. A formalization of the
entire block-cut tree or a maximal-clique decomposition is unnecessary
for this step. The separate chain-quotient proof still uses its existing
clique argument.

## Isolate the component once, for either recurrence

We use the following finite-sum observation with the same signed list of
whole components for K and E. Let a flip-closed layer L be partitioned into
whole components. Suppose C is its unique component having a specified
witness, and every other component D has an independently established
expression B_X(D). If a full-layer identity says X(L)=T_X, then

    X(C)=T_X-sum_(D!=C) B_X(D).                        (A2)

This is simply the disjoint sum X(L)=X(C)+sum_(D!=C) X(D). We use an
additive group because the correction coefficients are integers. The
algebra does not need a new coefficient system or a basis calculation.
Uniqueness is used only to justify that the listed correction procedures
cover all D!=C; it is not used to identify a raw target image as whole.

Here the witness is a connected state with every maximal corner covering
simultaneously. The three corrections are missing-corner deletion,
disconnected-block reordering, and alternating corner deletion. In the
last case all maximal corners are selected. We first mark them strict.
A maximal natural edge cannot be an exchanged short, so its membership
is constant throughout the whole component. Marking therefore preserves
the full component, not merely one state. This includes a corner unmarked
in the DD/ND step. We can now apply the strict-corner deletion theorem.

The inactive-witness cancellation is statewise, with a possibly different
redundant corner at each state. Its deletion images are unions of whole
smaller components by the existing component-refinement lemma. Neither
operation assumes the expansion for another component of the same area.

Use s=|selected relation| to index all layers in (A2). It includes strict
edges and does not change under remarking. NN has target layers s,s-1;
DN has target layer s. In the existing Lean orientation representation,
s=|D.strict|+theta.val.card. The exponent restored only at the end is
the ORIGINAL normal-edge count theta.val.card; remarking can change it.

## Attach from the right-marked equality

**One-mark attachment lemma.** Let P and a finite family P_i be whole
components on the same interval [0,c], and let m_i be integers. For each
fixed color beta, suppose BOTH valuations satisfy

    X(P)[beta]=sum_i m_i X(P_i)[beta],     X=K,E.       (A3)

For any whole component T on an interval [c,d], glue it at c to each
diagram, with no natural edges between interiors. Then

    X(P*T)=sum_i m_i X(P_i*T),            X=K,E,       (A4)

and every displayed product is a whole component. No expansion of T is
assumed. The source of identity (A3) is not a hypothesis of this lemma.

All triangles and cover tests belong to one side, since forward paths
cannot leave a side and return. Thus the flip graph is a Cartesian
product. For K, multiply (A3) by the beta-marked strict-coloring sum of T
with the weight of c omitted, and sum beta. For E, use the identical
operation on canonical HRV chain forests. Exactly the prefix fibre
ending at c merges with the attachment fibre containing c, whose least
vertex is c. Their chains glue to the chain of that merged fibre.
All other fibres remain unchanged. This proves (A4).

Omitting the endpoint weight is part of the definition of the attachment
factor, not polynomial division by x_beta. It works for every finite
alphabet, including the empty one. A one-vertex attachment has factor 1
at every prescribed color, so it gives the identity case directly.

Only one marked E signature is required: the size p of the fibre ending
at c, and the multiset of sizes of the other fibres. Its value is

    x_beta e_(p-1)(X_<beta) prod_(other fibres F) e_|F|.

Disconnected corrections put c's weak block last. This fixes c and
preserves that signature. Diamonds, redundant-edge changes and the
allowed contact swaps preserve the marked identities as proved in the
[endpoint note](COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#full-layer-recurrences-preserve-the-right-endpoint).
An unmarked equality alone would not be sufficient for (A4).

For the recurrence, all prefix diagrams have the same vertex interval.
The attachment therefore adds the same n, area and moment contributions
to every term. Strict decrease of (n,area,moment) is preserved. There is
no need to generalize the two-end attachment theorem: the initial path
already belongs to the prefix in the preceding lemma.

## Formalization order and existing interfaces

We keep two inductions separate. The path theorem uses vertex-count
induction only; the final valuation theorem uses (n,area,moment). Neither
the path theorem nor gluing assumes any component expansion. Proposed
order, with no new Lean declarations claimed in this audit:

1. Reuse ordinary forward diagrams, selected relations, actual flips and
   reachability. Add small interfaces for retaining maximal corners,
   induced-core cover tests, and path lifting.
2. Formalize preparation and the restored-exterior crossing slide. Then
   the complete-clique/parallel bases and last-clique inheritance, followed
   by initial-vertex inheritance using the two finite lemmas above. Finish
   no-articulation uniqueness and the initial-path extension.
3. Formalize component refinement for corner deletion, the three smaller
   corrections, the right-marked local NN/DN identities and (A2). This
   combines the two recurrences at one component-isolation interface.
4. Formalize (A3)--(A4), the area-prefix lemma and first-drop coverage.
   Apply the well-founded valuation induction; restore the original
   normal-edge weight last.

Related Lean, inspected read-only:

- `../../VerticalStripLLT/Circular/Flip.lean`: `DirectedFlipWitness`,
  `Flip`, `flipComponent`, `mem_flipComponent_iff` are the actual model.
- `../../VerticalStripLLT/Components/ForwardFlipNormalization.lean`:
  `DirectedFlipWitness.canonical_triple_order` and `normalizeForward`
  provide ordinary representatives of existing witnesses.
- `../../VerticalStripLLT/Components/UndecoratedComponents.lean`:
  `flip_toUndecorated_iff` and `flipComponent_toUndecorated` already give
  whole-component transport for strict-marking changes.
- `../../VerticalStripLLT/Components/IntervalDiagram.lean`:
  `Diagram.ofIntervalRelation` and `ofIntervalRelation_naturalEdge_iff`
  realize forward interval-closed relations, useful for induced diagrams.
- `../../VerticalStripLLT/Components/WordProof/ForwardHRV.lean`:
  `Orientation.liftedHRV_eq_coe_hrv_of_forward` links to actual HRV data.
- `../../VerticalStripLLT/Components/SelectedColoringTransport.lean`:
  `strictOrderEnumerator_selected_relabel` is the existing unmarked
  coloring transport; the new right-marked statement still needs proof.

Reuse declarations without pulling the completed expansion into the
argument. Some current interface files import word-specific machinery:
for example `ComponentSumPartition.lean` imports `ComponentCoefficient`.
Its finite partition operation can instead use `Finset.sum_fiberwise`
directly. If structural declarations need a narrower import boundary,
extract them in a later focused refactor while preserving public names.
This audit does not authorize a second component model or a symmetric
functions library. The one-vertex and empty cases remain explicit; the
existing circular `Diagram` representation requires positive n.

## Verification and retained limits

This round checked the written arguments, underlying source statements,
existing Lean interfaces, links, historical-prefix preservation and Git
diffs. No new computation, Lean build or replay of the unchanged finite
experiments was needed. Their exact scopes and frozen receipt remain in
the completion note. They are evidence, not the proof of these lemmas.

We retain the substantive limits: common-cover uniqueness is not asserted
at a fixed total size for arbitrary articulation graphs; paths may pass
through redundant-corner states; core restriction is not a whole-component
value map; an arbitrary adjacent swap need not preserve active membership;
and raw NN/DN images need not already be unions of whole components.
Signed component correction is still required. Formalization is the next
implementation task, not work completed by this audit.
