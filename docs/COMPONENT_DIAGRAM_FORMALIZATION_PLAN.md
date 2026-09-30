# Formalizing the ordinary component theorem by diagrams

Plan based on clean checkpoint `61ff6f8`, 2026-09-30. This is an implementation
plan, not a report of new Lean proofs. The mathematical inputs are the
[assembled diagram proof](proofs/COMPONENT_DIAGRAM_COMPLETION.md) and its
[cleanup audit](proofs/COMPONENT_DIAGRAM_AUDIT.md). Historical proof notes
remain the sources for the individual path constructions.

Implementation status: P0 and P2 are verified; P1 is partial. P0 and the
semantic import extractions are in `9d8c4bc`. P1 includes finite/lifted covers,
weak-block invariance, exact corner marking, source-only short flips
(`3bbb1e4`), convex path/cover restriction and an injective fixed-exterior
actual core-path lift (`bb86b82`). Specific induced-core geometry, swept
nonconvex transport and order reversal remain open.

P2 includes the state/component marked semantic bridge and both marked
diamonds with arbitrary exterior (`15ec74b`), closure invariance between
diagrams, the right-marked E signature by nonempty fibre sizes, and marked
K/E transport under sink-order-preserving relabelings. P3--P10 remain open;
the independent component theorem is not yet formalized. See `HANDOFF.md`
and `DiagramProofVerification.lean` for ownership and exact verification.

## Deliverable and scope

We will prove a second, independent Lean theorem with the same actual
semantics as the existing ordinary component theorem. Proposed declaration,
in `VerticalStripLLT.Circular`, with all names except the theorem name
already present in the repository:

```lean
theorem component_strict_eq_elementary_of_forward_by_diagrams
    {n : ℕ} {D : Diagram n} (θ : Orientation D)
    (hforward : ∀ e : Edge D.area, e.tail < e.head) (m : ℕ) :
    componentStrictEnumerator D θ m =
      evalElementary m (componentHRV D θ)
```

The new proof will use actual diamond paths, corner deletion, full-layer
NN/DN identities and right attachment. It will not invoke the existing
ordinary or circular component-expansion theorem, its word-functional
proof, or a fundamental-basis calculation. We retain the existing finite
polynomial model, including `XPoly`, `EExpansion` and `evalElementary`.

Corollaries restore the original normal-edge weight and reuse the existing
positivity/homogeneity theorems for `weightedComponentHRV`. We will expose
the same HRV expression for every alphabet, rather than defining an LLT by
the recurrence. Equality to the existing coloring sum is the main theorem,
not an optional semantic bridge at the end.

The ordinary forward specialization of `Circular.Diagram` is the existing
component model. Using its definitions does not require a circular theorem.
`Diagram n` already entails `0<n`; the empty ordinary diagram is handled
separately using the existing empty semantics. We do not introduce a second
flip graph or enlarge the diagram type to accommodate zero vertices.

## Representation decisions

| Object | Representation and reason |
| --- | --- |
| Natural diagram | Existing `Diagram n`, with explicit forward-edge hypothesis. Ordinary areas satisfy `a_j<=j`. |
| Selected state | Existing `Orientation D`. Its full selected set is `D.strict ∪ θ.val`; its stored set contains normal edges only. |
| Actual path | `Relation.ReflTransGen (Flip D) θ η`. Local constructors produce existing `DirectedFlipWitness` values. |
| Whole component | Existing `flipComponent D θ`, represented by a state θ. We need no new quotient type for components. |
| Weak connectivity | Undirected connectivity of the existing selected relation, as a derived graph view. No new state semantics. |
| All corners covering | A predicate on a state requiring every maximal natural corner to be selected and to cover. It is a witness condition, not a path invariant. |
| Anchor | Full selected set contains every maximal corner and only good normal edges, ordered by their corner-chain terminals. |
| Chain classes | Label each corner chain by its terminal vertex. Keep parallel copies as the original finite sets of good edges; do not require a multigraph library. |
| Layer index s | Cardinality of the full selected set: `D.strict.card + θ.val.card`. |
| Weight exponent k | `θ.val.card` in the ORIGINAL diagram. Restore it only after all representation changes. |
| K and E | Actual strict-coloring sum and evaluated actual HRV sum. A pair of values in `XPoly m × XPoly m` may package their common integer recurrence. |
| Induction order | Lexicographic `(n, area, moment)`, where `area=∑j a_j` and `moment=∑j j*a_j`. |

Use sorted order embeddings for induced vertex subsets. They transport
edges by endpoints into a new `Diagram`; equality of dependent `Edge` types
must be hidden behind transport lemmas. Order reversal is needed only for
path inheritance, not as an asserted equality of K or E.

The path theorem may first be stated for a saturated diagram, with all
maximal corners strict. Existing marking transport then gives the version
for a component selecting all corners in a less marked diagram. This keeps
the central induction's retained-edge obligations uniform.
Use absence of articulation vertices as the graph condition, with n<=2
handled explicitly. Do not encode it as unconditional connectedness after
every vertex deletion: deleting the only vertex gives the empty graph.

## Existing code: what is reusable and what still needs proof

| Existing source | Reuse | New obligation |
| --- | --- | --- |
| [Circular/Flip.lean](../VerticalStripLLT/Circular/Flip.lean) | `DirectedFlipWitness`, `Flip`, `flipComponent`, `mem_flipComponent_iff`, constant normal-edge count | Convenient ordinary triangle constructors and paths with prescribed endpoints/exterior |
| [Components/ShortEdges.lean](../VerticalStripLLT/Components/ShortEdges.lean) | `Diagram.admissible_of_forward`, `orientationOfForward`, natural-short normality | Full-set adapters and ordinary corner predicates |
| [Components/ForwardFlipNormalization.lean](../VerticalStripLLT/Components/ForwardFlipNormalization.lean) | `canonical_triple_order`, `normalizeForward` | Restriction/lifting through induced cores and order reversal |
| [Components/UndecoratedComponents.lean](../VerticalStripLLT/Components/UndecoratedComponents.lean) | `flip_toUndecorated_iff`, `flipComponent_toUndecorated` | Convenient partial marking/saturation transport, preserving total count and marked semantics |
| [Circular/CornerDiagram.lean](../VerticalStripLLT/Circular/CornerDiagram.lean) | `Diagram.strictify`, `deleteCorner`, lowered area and edge inclusion | Actual whole-component deletion/refinement and marked valuation transport |
| [Components/IntervalDiagram.lean](../VerticalStripLLT/Components/IntervalDiagram.lean) | `ofIntervalRelation`, `ofIntervalRelation_naturalEdge_iff` | Strict corner markings and component maps for induced, deleted and reordered diagrams |
| [Components/ForwardHRV.lean](../VerticalStripLLT/Components/ForwardHRV.lean) | Forward reachability and `liftedHRV_eq_coe_hrv_of_forward` | Canonical chain-forest and marked fibre evaluations |
| [Circular/HRVEvaluation.lean](../VerticalStripLLT/Circular/HRVEvaluation.lean) | `Orientation.evalElementary_hrvMonomial` | One-end marked version and attachment gluing |
| [Circular/ComponentSemantics.lean](../VerticalStripLLT/Circular/ComponentSemantics.lean) | Actual component sum, component equality, no-normal base, common weight | Whole-component restriction/product transport and new recurrence proof |
| [Circular/FirstBounceRecurrences.lean](../VerticalStripLLT/Circular/FirstBounceRecurrences.lean) | NN target geometry and existing aggregate identities | Total-edge-layer and right-marked NN identity; an aggregate identity alone is insufficient |
| [Circular/OneBounceDNData.lean](../VerticalStripLLT/Circular/OneBounceDNData.lean) | Concrete DN target and hypotheses | First-drop constructor, layer/mark preservation and strict moment decrease |
| [Components/ComponentPositive.lean](../VerticalStripLLT/Components/ComponentPositive.lean) | Positivity and degree of the actual HRV expression | Connect it to the new diagram-based semantic theorem |

Three small import issues should be resolved before importing those APIs into
the new proof. `SelectedColoringTransport.lean` imports `ComponentScalars`,
which brings word machinery; the selected-coloring finite-sum lemma there
can be moved to a lower-level semantic module, retaining its public name.
Then the existing relabeling proof can import that module.
`ForwardHRV.lean` also imports `BlockExtractor` and `BlockCancellation`
through its structural and signed-word results. Extract its structural
prefix through `hrv_le_of_reachable_forward` into `ForwardHRVBasic.lean`,
preserving names and making the old module import the new one. Move the
fibre-restricted reachability lemma only if needed, with its small induced-
relation definition separated from word compatibility. Finally,
`ComponentSumPartition.lean` imports `ComponentCoefficient`; we can group
finite component sums with `Finset.sum_fiberwise` or a local representative
partition instead. Do not import the coefficient module just for grouping.

A read-only import traversal and source inspection at this checkpoint found
no old word-proof dependencies in the closures of `Circular.Flip`,
`ComponentSemantics`, `UndecoratedComponents`, `ForwardFlipNormalization`,
`IntervalDiagram`, `FirstBounceRecurrences`, `OneBounceDNData`,
`HRVEvaluation` or `ComponentPositive`. This was a source import check,
not compilation or a theorem-dependency certificate.

## Modules, interfaces and checkpoints

New modules will live under `VerticalStripLLT/Components/DiagramProof/`.
The names below are proposed; no such Lean files or declarations have been
created by this plan. Split a module further only when a coherent proof or
compile-time boundary warrants it. Each numbered checkpoint must compile
without placeholders before it is committed and pushed.

### P0. Establish the independent proof boundary

Create a minimal `Basic.lean` importing only the existing semantic/flip
interfaces needed initially. Give names to the forward hypothesis, full
selection and total count; prove their adapters to existing definitions.
Record the import closure and available cache/build ownership. If the
coloring-sum or forward-HRV extraction is needed immediately, move the
structural declarations to low-level files and change only their import
sites, preserving their names. Otherwise do those extractions at P2.

Acceptance: the module and affected old dependents compile; full selection
has the expected cardinality; admissibility follows from forwardness; the
new module imports no old component expansion or word-functional route.
This is the first implementation checkpoint, not a skeleton theorem with
the desired result left as an assumption.

### P1. Ordinary paths and exact component transport

Modules: `PathTransport.lean`, `CornerTransport.lean`.

Prove finite ordinary cover tests agree with the existing integer-lift
tests. Build an ordinary triangle-flip constructor, using forwardness to
discharge the cyclic window and existing short-normality lemmas. Establish
that a flip preserves the full selected count and selected weak blocks.

Prove corner selection is constant along a path, partial remarking preserves
a whole component, and a path in an induced core lifts when forward paths
between core vertices cannot leave and return. Separate three uses: convex
intervals, deleting the initial vertex, and a swept nonconvex core. The
last needs a selected-exterior invariant, not just a natural-graph claim.
For each core construction, prove which maximal corners survive, verify
their strict markings remain legal, and identify any new maximal corners.
The two inheritance cores avoid new unwanted corners by their specific
geometry; this is not true of arbitrary induced subdiagrams.

Provide order-reversal transport of actual paths, including strict-edge
and cover correspondence. No reversal theorem for valuations is required.

Acceptance: maps used as whole-component equivalences have both directions
and surjectivity onto the complete target component. A one-way path lift
is labeled only as a lift. Core restriction is never claimed to be a
component equivalence merely because some paths lift.

### P2. Marked semantic identities and the semantic bridge

Modules: `MarkedValues.lean`, `LocalIdentities.lean`.

Define K at fixed color beta of the greatest vertex by filtering actual
strict colorings. Define marked E using the increasing chain on each actual
HRV fibre, as an auxiliary relation or an ordered-fibre coloring predicate.
These chains need not themselves form a natural diagram, so do not package
their union as a `Circular.Diagram`. Prove summing beta recovers the existing
state K and `evalElementary m θ.hrvMonomial`. Lift these equalities to component
sums. This connects the marked proof machinery to the actual target before
we use any recurrence.

Prove the right-marked E signature: the size of the greatest-vertex fibre
and the multiset of the other fibre sizes determine its value. Prove the
diamond identity for K pointwise in colors and for E by equality of the
two-element multisets of full HRV maps. Add closure-invariant edge changes
and sink-order-preserving relabelings that fix the marked endpoint.

Acceptance: these identities hold for every finite alphabet and arbitrary
permitted exterior. The empty alphabet is included. Marked E is not defined
as marked K on the original relation; its defining relation is the HRV
chain forest. No basis independence is used.

### P3. Preparation and crossing slides

Modules: `CornerChains.lean`, `Preparation.lean`, `CrossingSlide.lean`.

Prove maximal corners form increasing disjoint chains. Define their terminal
map r and the good-edge set A*. Establish that subsets of A* containing
all corners have all corners covering. Conversely, construct the ordered
preparation path from a common-cover state to its anchor, preserving total
count and weak connectivity.

Also prove here that each unordered pair of corner chains has at most one
auxiliary short-edge path, with good copies in increasing endpoint order.
This supplies the positions for parallel-copy rearrangement and P4's
two-chain base; it must precede those uses rather than wait for P5.

Formalize the four-stage crossing slide retaining (a,c) and (b,d), with
a<b<c<d: sweep outgoing obstructions, sweep incoming obstructions, perform
the two central flips, and restore both sweeps. Its contract replaces ab
by cd while retaining ac,bd and restoring every other edge. Only the two
retained longs need to cover initially; other corners may be redundant
during the path. The exchanged edges must be normal in the ambient diagram.

Source: [preparation](proofs/COMPONENT_NN_REDISTRIBUTION.md#normalize-entire-corner-chains-allowing-temporary-redundancy)
and [restored-exterior slide](proofs/COMPONENT_NN_REDISTRIBUTION.md#sweep-aside-the-obstructions-and-restore-them-after-the-slide).

Acceptance: prove the exact endpoint selection and all intermediate flip
witnesses. Sweep induction uses a finite ordered list, not search through
the entire flip component. Extract unrestricted fixed-count rearrangement
of parallel copies as a corollary.

### P4. Complete-clique paths and the finite connectivity helpers

Modules: `FiniteConnectivity.lean`, `CompleteClique.lean`.

Prove forest extension to connected edge sets of every feasible size,
including avoidance of one removable nonrequired edge. Prove subset-band
connectivity with its one-level exceptions and fixed-count exchanges through
overlapping sets of positions. Use the statements in the cleanup audit;
keep cardinality equations additive to avoid truncated subtraction.

Formalize the complete-clique theorem in its two parts: reach the fixed
chain, then rearrange the extra chords. Include interval opening/closing,
the outer-chord column sweep, and the explicit four five-vertex paths from
the source table. Those finite bases are actual lists of flips checked by
Lean, not external enumeration assumptions. Kernel-checked `decide` may
close genuinely small decidable facts; do not introduce unchecked native
proofs or enumerate arbitrary component graphs.

Extract its local version for one selected weak block inside a corner
interval, using P1's no-return lifting. Also prove the elementary
reachability-forcing path used in last-clique inheritance: shrink a Hasse
path's label hull by incoming/outgoing cover forks, then normalize within
the hull. Record which interior selected connections survive; do not claim
arbitrary exterior remains fixed while the hull is shrinking.

Source: [complete-clique theorem and base paths](proofs/COMPONENT_NN_REDISTRIBUTION.md#complete-diagrams-every-connected-active-layer-is-one-component).

Acceptance: common-cover states of each feasible size connect using only
paths. No component expansion is used. The two-chain case follows from
parallel-copy rearrangement, and the small vertex cases are explicit.

### P5. Chain quotient and last-clique inheritance

Modules: `ChainQuotient.lean`, `TerminalClique.lean`, `LastClique.lean`.

Use P3's auxiliary short-edge paths to prove that good copies retain exactly
the natural adjacencies between chain
classes. Obtain connectivity of A*, feasible anchor sizes, and the quotient
no-articulation/no-bridge consequence needed for edge removability. We need
these concrete consequences, not a new general interval-graph library.

Formalize terminal-clique occupancy transfer with capacities. A transfer
that obstructs connectivity uses the proved temporary class repair; the
sum of occupancy discrepancies decreases. Lift these transfers by the
complete-clique paths and crossing slides.

Then prove last-clique inheritance through its four separate claims:
make the selected core connected; sweep and lift core paths with exact
exterior restoration; reach the fixed spanning tree; rearrange extra
positions using the common buffer edge. Obtain first-clique inheritance
by the order-reversal path theorem from P1.

Sources: [chain quotient](proofs/COMPONENT_NN_REDISTRIBUTION.md#the-interval-graph-of-corner-chains),
[terminal clique](proofs/COMPONENT_NN_REDISTRIBUTION.md#complete-recurrences-when-the-last-clique-contains-every-chain-terminal),
[last-clique inheritance](proofs/COMPONENT_NN_REDISTRIBUTION.md#extending-the-last-clique-from-a-connected-core).

Acceptance: the hypothesis is uniqueness in the strictly smaller core,
not the general theorem currently being proved. Every local path preserves
required edges, and every claimed restored exterior has an endpoint equality.
The clique transfer argument is a prerequisite, not an unproved black box.

### P6. Initial-vertex inheritance and general path uniqueness

Modules: `InitialVertex.lean`, `CommonCoverUniqueness.lean`.

For first corners 0a,1b, prove deletion of 0 loses exactly 0a and preserves
all remaining chain terminals. Establish the disjoint decomposition

```text
A*(G) = {0a} ∪ A*(G') ∪ {0v : v∈J},
d_v = a h_v,       J={v : 0<v<a and r(v)>r(a)}.
```

Prove the matching d_v is natural, normal and good. Use crossing slides to
reduce the number of selected core components, then lift paths within a
fixed extra set S. For adjacent feasible S, the forest-extension lemma
constructs a connected core witness omitting d_v. The crossing slide links
these sectors; the subset-band theorem joins all sectors. Feasibility is
expressed as `r<=t<=m` and `t+1+S.card=s`.

Perform strong induction on vertex count: complete/two-chain bases from
P4; first-clique trimming when the second tail exceeds 1; initial-vertex
inheritance otherwise. In the latter case P5 supplies removability of
each d_v. Prove the forced initial-path extension afterwards.

Source: [initial-vertex inheritance and uniqueness](proofs/COMPONENT_NN_REDISTRIBUTION.md#initial-vertex-inheritance-through-extra-edge-sectors).

Acceptance: the resulting theorem connects any two connected common-cover
states of the same total size for a natural graph without articulation,
and for its initial-path extension. It does not require intermediate
common-cover states. It does not assert uniqueness at a fixed total count
for arbitrary graphs with articulations.

### P7. Smaller component corrections and envelope normalization

Modules: `CornerDeletion.lean`, `BlockReordering.lean`, `Envelope.lean`.

Prove absent-corner deletion is an exact whole-component map. Prove strict
corner deletion, under the normal-selection identification, removes only
flips using that corner as retained long. Thus a whole source component is
a union of whole deletion components. Iterate for a finite corner set.

Use redundant-corner closure invariance to prove alternating deletion for
a component with no common-cover witness. First re-mark all selected
maximal corners strict. The redundant corner may depend on the state.
Both marked valuations must have exactly the same integer coefficients.

For disconnected selected relations, reorder the invariant weak blocks
into consecutive intervals, placing the block of the greatest vertex last.
Prove whole-component equivalence, ordinary target validity, marked K/E
preservation and strict natural-area decrease when the source natural
graph is connected.

Finally implement the selected-interval envelope by repeated deletion of
absent maximal corners and marking the remaining maximal corners. Record
which steps strictly decrease area and which are representation changes.

Sources: [corner differences](proofs/COMPONENT_CORNER_DIFFERENCES.md#a-signed-recurrence-in-whole-smaller-components),
[envelope](proofs/FLIP_COMPONENT_INDUCTION.md#the-minimum-area-realization-is-the-saturated-envelope),
[marked reordering](proofs/COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#full-layer-recurrences-preserve-the-right-endpoint).

Acceptance: corrections yield whole components with strict measure
decrease, independently of any equally large component identity. Envelope
normalization preserves the original selected relations and both values.

### P8. Marked full layers and isolation of one component

Modules: `LayerRecurrences.lean`, `ComponentReduction.lean`.

Use the existing ordinary NN/DN geometries but prove the required identities
with a fixed total-edge layer and fixed right-endpoint color. Build them
from P2's local identities and the actual finite layer splits. Aggregate
LLT recurrences alone do not provide either refinement.

Prove the local target decreases here from the eligible contact hypotheses:
NN decreases natural area; forward DN preserves area and decreases moment
by t-y>0. These geometry lemmas do not depend on first-drop selection.
P9 will construct their hypotheses for the chosen source contact.

Define a small finite reduction certificate. Each term contains a target
diagram on the SAME vertex set, a representative of one whole component,
and an integer coefficient. The certificate records forwardness, smaller
measure and paired K/E equalities, uniformly in alphabet and, for the
marked version, endpoint color. Repeated target components may occur;
combining duplicates is optional and need not burden the proof.

Component isolation uses P6: all other source components have one of the
three independent P7 corrections. Complete the source layer, apply NN or
DN, and subtract those corrections. NN outputs layers s and s-1; DN
outputs layer s. No definition of a target image is treated as proof of
its closure under flips. The targets are whole by their construction.
Choose exactly one representative per source component when partitioning
the layer; summing a component once for every state would overcount. This
partition multiplicity is distinct from deliberate repetition of signed
terms in the output certificate.

Acceptance: construct the same finite coefficient list for K and E,
independent of m and beta. The marked certificate fixes the greatest vertex
in every relabeling. All final terms have a certified strict decrease.

### P9. Right attachment, prefix selection and first-drop coverage

Modules: `RightAttachment.lean`, `FirstDrop.lean`.

Prove the Cartesian-product theorem for flip components in two diagrams
meeting at an endpoint. Prove strict-coloring gluing and the HRV fibre
merge formula. Define endpoint-omitted weights by products over the other
vertices, not division by a polynomial variable. From any right-marked
paired equality on a fixed interval, obtain the attached equality using
the same coefficient list. The attachment's K=E identity is not assumed.

Prove the area test for articulations and select the first run of area
entries at least 2. This gives an initial-path/no-articulation prefix and
an arbitrary right attachment. Prove the first strict drop agrees in
prefix and source, including the one-vertex attachment.

Construct the four first-drop contact cases with their exact geometry.
For DD/ND, unmark the obstructing upper corner and use P1 to identify the
same whole component. Then use forward DN or NN, applying the P8 target-
decrease lemmas. Prove adding a fixed right attachment preserves those
decreases.

Sources: [right attachment](proofs/COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#arbitrary-right-hand-attachments),
[area prefix](proofs/COMPONENT_DIAGRAM_AUDIT.md#choose-the-prefix-directly-from-the-area-sequence),
[first drop](proofs/COMPONENT_RECURRENCE_COVERAGE.md#the-first-drop-lemma).

Acceptance: obtain a smaller-component certificate for every connected,
non-path ordinary component after normalization and the direct corrections.
An unmarked equality is never used as input to the attachment lemma.

### P10. Well-founded induction, weights and integration

Modules: `Expansion.lean`, `Consequences.lean`; focused audit entry point
`DiagramProofVerification.lean` at the repository root.

Prove disjoint natural-component factorization into smaller vertex sets
with exact product components and multiplicative K/E. The connected path
base is the saturated increasing chain, with value e_n. The one-vertex
case is included. The empty semantics remains a separate base statement.

Run strong induction on the lexicographic triple. Envelope deletion and
the P7 corrections reduce area; natural disconnection reduces n; P8/P9
give strict smaller targets with the same signed coefficients. Mere
remarking invokes no induction hypothesis. This yields the public theorem
stated at the start.

Restore the original normal-edge exponent using the existing constant-count
lemma. Prove the weighted theorem and positivity corollary with new diagram-
route names. Preserve the existing public ordinary and circular theorems;
do not replace their proofs as an incidental integration change.

Acceptance: the final theorem has no assumptions asserting any of the new
connectivity or recurrence obligations. Its conclusion is the existing
semantic equality, for every forward diagram, orientation and alphabet.
Add the finished modules to the umbrella only after the independent focused
entry point passes its proof-dependency and axiom checks.

## Dependency order and first implementation batch

The main path dependency is

```text
P0 -> P1 -> P3 -> P4 -> P5 -> P6
```

The semantic side is `P0 -> P2`; P7 needs P1 and P2. P8 joins P2, P6 and
P7. P9's attachment and area geometry can be developed before P8, but its
general recurrence conclusion needs P8. P10 joins all of these, plus
disjoint factorization and the elementary chain base. The initial path
induction and final valuation induction remain separate throughout.

Begin with P0 and the ordinary triangle constructor/cover bridge of P1.
Next prove a restored-exterior crossing slide from P3 and the marked
semantic bridge from P2. This tests the two interfaces most likely to
cause expensive rewrites before implementing all the longer path proofs.
Then follow the path dependency to P6, complete P7/P8, and finish P9/P10.
This is a sequence for one primary builder, not authorization to launch
parallel build workers.

## Verification and checkpoint discipline

Pinned environment: Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Recheck manifests and build-slot
ownership at implementation time. The currently registered Lean MCP is
rooted at `RealRooted`; do not invoke its builds against this project.
AXLE can support isolated experiments but never replaces the local checks.

At each checkpoint, build only its modules and any existing modules whose
imports or declarations changed. For example, after the proposed file exists:

```sh
timeout 20m nice -n 10 lake-workspace build \
  VerticalStripLLT.Components.DiagramProof.CrossingSlide
```

Run one Lean job at a time, keep output under `/lake-cache/ai-projects`,
and monitor a long job without starting a second replay. No `lake update`,
plain Lake invocation, or new dependency is part of this plan.

Each checkpoint records its exact new declarations, focused build result,
axiom output, remaining obligations and ownership in `HANDOFF.md`, then
commits and pushes only owned files. Use targeted `#print axioms` checks
for the completed interface theorems. Accept only the project's usual
`propext`, `Classical.choice`, `Quot.sound`; reject proof placeholders,
custom axioms and unchecked native proofs. Check changed Lean source for
`sorry`, `admit`, `native_decide`, custom `axiom` declarations, line lengths
and whitespace. Examine matches rather than confusing comments with proofs.

At P10, `DiagramProofVerification.lean` imports the new theorem module
directly, not `VerticalStripLLT`. Audit its transitive imports and theorem
dependencies to exclude the old component proof. An axiom inventory alone
cannot establish independence, since the old proof has the same axioms.
Run the focused build and its axiom entry point first. A final full build
and existing `Verification.lean` audit are warranted when the new modules
are exported through the umbrella or an old shared interface was moved;
they are integration checks, not a loop to repeat after every local lemma.

Retain the exact Rust receipts as research evidence. They are not Lean
premises, and broad component enumeration is not a required recurring test.
Use the explicit small flip lists and delicate boundary cases for focused
formal examples: redundant intermediate corners, empty/full subset bands,
absent unmarked corners, all four contact types, a path prefix, and the
one-vertex right attachment.

## Main risks and completion criteria

The largest proof work is P3--P6, especially restored exterior, complete-
clique chord paths and last-clique occupancy transfer. They should not be
hidden inside a single generic normalization theorem. The main interface
risks are dependent edge transports, component surjectivity, the distinction
between total and normal counts, and preserving the right endpoint through
disconnected corrections. Each has an explicit acceptance test above.

We should not spend effort proving global uniqueness for articulation
graphs, making every intermediate corner cover, or constructing a universal
two-end attachment theorem: none is needed and the first two would conflict
with the recorded examples. Finite layer subtraction is sufficient; a
general symmetric-function or linear-system library is unnecessary.

The work is complete when the independent semantic theorem, its weighted
and positive consequences, and all required path/recurrence lemmas compile
without placeholders; focused and necessary integration checks pass;
proof dependencies exclude the old expansion route; and the source and
verification record are pushed with an up-to-date handoff. The paper proof
is complete already. The implementation status above distinguishes the
verified source increments from the remaining checkpoints.

## Review and planning verification

The independent Astra reviewer `diagram_audit` inspected the concrete plan
and approved its contracts and acceptance conditions with two dependency-
order corrections, now incorporated: auxiliary short-edge paths and ordered
copy positions belong in P3, before the two-chain base; local NN/DN target
decreases belong in P8, before certificates require them. It also checked
the HRV/import extraction, auxiliary-relation definition of marked E,
whole-component representative multiplicities, no-return core lifting,
strict corner validity and small graph cases.

Primary inspected the listed Lean declarations and current import paths,
the longer complete-clique and terminal-clique proof dependencies, and the
existing toolchain/verification entry points. This turn changes only this
plan and `HANDOFF.md`. No Lean sources, proof notes or build configuration
were changed, and no Lean or Rust build or mathematical experiment ran.
