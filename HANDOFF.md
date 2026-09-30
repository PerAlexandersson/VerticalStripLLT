# VerticalStripLLT handoff

## Active implementation — P0/P2/P3 complete, P1/P4 partial

Current continuation began clean at pushed `8395f6e`; the previous turn
made verified progress. The current increment proves the single-chord path,
the complete-diagram induction step for greatest label `n >= 5`, and the
small cases `n <= 3`. The remaining complete-diagram base is `n = 4`.

Primary owns all `DiagramProof/` files, `DiagramProofVerification.lean`,
this handoff and the formalization plan, and retains the sole serialized
build slot. Luna returned `ChainStateSelection`; Terra returned
`ChordSubsetChoice`. Primary repaired and verified both, and wrote
`SingleChord`, `ChordOuterExchange`, `ChordConnectivityStep` and
`CompleteSmall`. Terra independently audited the singleton and outer paths,
cardinality split and normalization counts. Both agents are finished, and
all current source is primary-owned. Historical proof notes and unrelated
ownership remain unchanged.

The independent component theorem is unfinished. The active goal also
requires a new illustrated draft combining the circular e-expansion and the
ordinary diagram-based component proof in the authors' style; writing has
not started. No old word/scan proof or fundamental-basis route is imported.

The user explicitly invoked the
[combinatorics paper-writing skill](/home/dev/.codex/skills/combinatorics-paper-writing/SKILL.md).
Primary read it and its notation/author-style references. The user also
asked us not to invent terminology without strong motivation. Use established
terms or state the condition itself, follow Robin and the author's diagram
reasoning, and keep implementation/audit details out of the manuscript.
No fundamental-basis or old word/scan argument is used.

### Current P4 increment — complete-diagram induction step

- `ChainStateSelection` gives the exact selected relation for an actual chain
  state, and its singleton specialization. No extra edges are silently
  dropped when switching between the relation and finite-set descriptions.
- `SingleChord.complete_singleChord_path` opens to `2`, flips `13 -> 01`
  across `03`, then `01 -> 1n` across `0n`, and closes. Exact endpoint
  relations prove the path from `P_n + 13` to `P_n + 1n` for `n >= 3`.
  `completeChainState_singleChord_reachable` expresses it using chord sets.
- `ChordOuterExchange` identifies the endpoint of CC4 with the actual chain
  state for `insert (1n) (S.erase (13))`, provided `13,2n` are selected and
  `1n` is absent. It compares full selected sets, not just chord counts.
- `ChordSubsetChoice` uses Mathlib's finite subset extension theorem to
  choose an equally large subset containing prescribed `13,2n` and avoiding
  `1n`. No chord-count formula or binomial arithmetic is needed.
- `ChordConnectivityStep.completeChainState_reachable_of_smaller` joins all
  equal-size chord sets for `n >= 5`, assuming connected active-layer
  connectivity for strictly smaller complete diagrams. Equal outer choices
  use interval rearrangement; differing choices use the singleton path at
  count one or CC4 at count at least two. Empty and full sets fall under the
  equal-outer case automatically.
- `complete_reachable_of_smaller` normalizes two connected states covering
  `0n` to chains and transports total selected counts along both paths. It
  then applies the chord step. The smaller-diagram assumption remains
  explicit; this is NOT yet the unconditional complete-layer theorem.
- `CompleteSmall.complete_reachable_of_le_three` proves the active-layer
  theorem for `n <= 3`. There is at most one chord position, so equal-size
  chord sets agree after normalization. A cover of `00` is impossible.

Terra's read-only audit found no gap in the singleton bridge, exact outer
exchange, cardinality cases or count transport. The theorem concerns
connected states with the extreme corner covering, exactly as required by
the complete-diagram induction; arbitrary connected states are not claimed.

The attempted five-vertex helper from Luna was discarded before building or
committing it: it represented intermediate states with `completeChainState`,
which incorrectly reinserted the chain edge just removed by a flip. This is
an implementation error, not a defect in the written flip table. The first
row's actual full selections are:

```text
{04,12,23,34,13} -> {04,12,23,13,03} -> {04,12,13,03,02}
 -> {04,12,03,02,01} -> {04,12,03,02,14}
 -> {04,12,03,14,23} -> {04,12,14,23,34}.
```

Implement the four table paths using actual orientations built from their
full selected relations/sets, and identify their endpoints with chain states
only after all chain edges have been restored. No `FiveVertexPaths.lean`
file remains, and none of those four paths is claimed Lean-verified.

### Earlier P4 increment — outer-chord move (`8395f6e`)

- `OrderedSweep` now also allows the outgoing cutoff to equal the retained
  edge's head. Every moved pivot is still strictly below that head. All old
  strict-cutoff APIs and the incoming-sweep APIs retain their statements.
- `ColumnSweep.exists_columnSweep` proves the exact CC6 endpoint
  `A - 12 + 1n` whenever the root row contains only `0n`, `12` and `2n` are
  selected, and `1n` is absent. After the incoming sweep, every positive edge
  into `n` is absent. The middle `12 -> 01` flip preserves this, proving that
  `0n` still covers before outgoing restoration. Arbitrary other chords are
  allowed. This theorem works on any forward diagram meeting its hypotheses.
- `ChainOpening` and `CompleteOpening` now offer versions requiring only the
  adjacent edges at or above the opening threshold. Existing whole-chain
  theorems wrap these versions. `IntervalPaths` uses the weaker assumption
  to open and close endpoints which can have missing edges below the interval
  top, while restoring the complete exterior.
- `ChainRepair.complete_chain_repair` opens to `3`, restricts to the actual
  four-vertex diagram, applies the four proved child-merging flips, and
  closes. It replaces exactly `13` with `12`, starting with `12` absent and
  `13,23` selected. No smaller-connectivity hypothesis is used.
- `OuterChordMove.exists_complete_outerChordMove` combines the sweep and
  repair into CC4. For a chain state with `13,2n` selected and `1n` absent,
  its actual flip path ends at `A - 13 + 1n`, with every other selected edge
  restored. The four named vertices satisfy `0 < 1 < 2 < 3 < n`.

Terra's independent audit found no mathematical gap. Exact selected-relation
identities identify the final actual orientations; no enumeration or assumed
local path substitutes for the explicit flips. The single-chord path and
cardinality-indexed step are now supplied by the current increment above.

### Earlier P4 increment — chord rearrangement (`58a7bf1`)

- `CompleteChords` constructs chain states in the actual orientation type,
  recovers every state satisfying the root-row and consecutive-chain
  conditions, and splits its total selected count into chain and chord counts.
- `SubdiagramCounts` embeds actual edges along the vertex embedding. Equal
  global selected counts and equal full exterior selections imply equal
  restricted selected counts, including cross-boundary exterior edges.
- `IntervalCounts` applies this after opening, then invokes the explicitly
  assumed smaller active-layer theorem to obtain the local CC3 path.
- `ChordIntervals` covers every chord except `1n` by `[1,n-1]` and `[2,n]`.
  For `n >= 5`, their overlap contains `24`. It supplies actual embedded
  endpoint witnesses and identifies the excluded outer chord.
- `ChordExchange` realizes each exchange within either interval by actual
  flips. Its endpoint is exactly `S-e+f`, with every other edge restored;
  the invoked complete diagram has strictly fewer vertices.
- `FixedPositionPaths` combines exchanges through overlapping position sets,
  using the existing occupancy-aware finite-subset path lemma. Local paths
  may leave the endpoint subtype; their reflexive-transitive closures are
  composed and flattened, without assuming invariants at intermediate steps.
- `ChordRearrangement.complete_chain_reachable_of_fixed_outer` connects actual
  chain states with equal total selected counts and the same `1n` membership,
  assuming connectivity on smaller complete diagrams. This is an endpoint
  reachability theorem: it does NOT assert that `1n` membership is preserved
  at every flip on the resulting path.

Terra's independent audits found no gap in the count cancellation, exact
exterior restoration, strict size decrease or occupancy-aware exchanges.
The smaller connectivity statement remains an explicit induction hypothesis.
At that checkpoint changing the outer chord, the small bases and
complete-layer connectivity remained unfinished. CC4--CC6 are now verified
as described above; the final complete-layer theorem remains open.

### Earlier P4 increment — interval paths (`64205a9`)

- `CoreExtension.liftDirected_of_cover_iff` extracts the actual flip-lifting
  proof with explicit inside relation, unchanged exterior, and exact cover
  tests. It does not assume convexity; the previous convex API is preserved.
- `PathRestriction` restricts paths and covers when every vertex on a path
  between image vertices lies in the image. It proves this for `{0} ∪ [a,b]`
  in a forward relation whose root row has no positive head below a.
- `CompleteSubdiagram` constructs restriction/extension along an increasing
  vertex embedding, with exact selected relations and unchanged exterior.
  Equal exteriors identify the extended restriction with the target state.
- `CompleteInterval` constructs the concrete embedding `0,a,...,a+m`, proves
  its exact image, and proves actual local path lifting uniformly for every
  intermediate local state. This is not an assumed convex core.
- `ChainOpening.exists_chain_opening` proves the descending adjacent swaps
  `j(j+1) -> 0j`, with an exact selected-relation endpoint and arbitrary
  chords fixed. `CompleteOpening` identifies that endpoint with an explicit
  actual orientation, and gives the smaller chain's root row and consecutive
  edges after restriction.
- `ChainConnected` derives directed reachability to the greatest vertex,
  selected connectivity and the extreme cover from those chain conditions.
- `IntervalPaths.complete_interval_chain_path` opens two ambient chain
  states, lifts a supplied path between their smaller restrictions, then
  reverses the second opening. Its final endpoint is the prescribed target,
  restoring the full exterior. The input states must agree on every selected
  pair with an endpoint outside the interval image.
- `openCompleteChain_interval_connected_cover` supplies the connectedness and
  active-corner hypotheses needed for the smaller complete-diagram theorem.

Terra independently audited CC3 and found no exterior-restoration or cover
restriction gap. At that checkpoint the local path was an explicit input, and chord
rearrangement and complete-layer connectivity remained open. The present
increment supplies count transport and uses that path with an explicit
smaller-connectivity hypothesis, as recorded above.

### Earlier P4 construction — CC1 and CC2

- `CompleteDiagram`: the complete forward diagram on `Fin (n+1)`, concrete
  edges by endpoints, and its unique maximal corner `0n` when `0<n`.
  The area sequence is defined directly; the one-vertex diagram also exists.
- `FiniteCoverPaths`: finite forward reachability decomposes into cover
  paths. Unique outgoing covers give comparable reachable vertices and
  consistent terminal sinks.
- `ForkNormalization`: actual directed flips eliminate outgoing cover forks
  by increasing the bounded sum of selected-edge tails. A least-vertex row
  with at most one selected neighbor is preserved exactly.
- `CoverReachability`: with unique outgoing covers, a connected selected
  graph reaches the greatest vertex from every vertex. A cover to that
  greatest vertex is the only selected outgoing edge of its source.
- `ChildMerge`: the four actual flips of CC2 replace exactly `it` by `ij`,
  restoring every other selected edge. `ChildMergeCovers` proves that this
  replacement preserves uniqueness of outgoing covers.
- `TerminalChildren`: repeating CC2 decreases the number of all selected
  edges entering the greatest vertex. Eventually its only cover predecessors
  are the least vertex and the greatest vertex below it. Moving the latter
  edge to the prefix leaves every prefix vertex able to reach its top.
  Non-cover incoming chords are allowed and are not claimed absent.
- `SingleCorner`: the exact terminal map and prepared least-vertex row for
  one extreme corner. `CompletePrefix.exists_connected_prefix_of_single_corner`
  combines preparation, fork elimination and child merging into an actual
  flip path to the connected-prefix state, with both extreme edges covering.
  Its strict three-vertex inequalities exclude the small bases.

Terra's independent read-only audit found no defect in the CC1/CC2
contracts. The current continuation now completes the following next step:

- `SelectedRelation`: build an actual orientation from a relation whose
  edges are natural and which contains the strict edges; exact selected
  relation and reconstruction of an existing state.
- `CompleteRestriction`: remove the last vertex, extend an arbitrary prefix
  state with the unchanged top edges, and prove exact restriction/extension,
  cover and path restriction, connectedness, and actual flip-path lifting.
  This instantiates `CoreExtension`; no whole-component equivalence is inferred.
- `CompleteChain.exists_complete_chain`: every connected state covering the
  extreme corner in `completeDiagram (n+1)` reaches a state containing
  `0(n+1),12,...,n(n+1)` and no other edge out of 0. Induction starts at two
  vertices. After the prefix path the penultimate vertex is a sink because
  its top edge is still absent; this re-establishes both covers for the final
  reverse move. The top corner need not cover during the lifted local path.
- Extracted `relationCover_of_other_sinks` from `ChildMerge` as a public lemma
  and reused it for these final cover tests. No new state predicate is needed.

Terra independently reviewed the unmarked induction and its endpoint
requirements. The chain theorem uses actual unmarked orientations with an
explicit active-corner hypothesis. `exists_complete_chain_marked` also compiles, keeping the extreme corner
strict at every intermediate state via the existing marking equivalence.
`selected_markCorner_iff` records the unchanged selected relation. No change
of component semantics is made.

### Earlier verified interfaces

- `9d8c4bc`: independent imports, full selections/layers, finite/lifted covers
  and weak-block invariance; affected old consumers compile.
- `3bbb1e4`: source-cover short flips and exact corner marking of whole
  components, both directions/surjectivity, HRV and coloring values.
- `15ec74b`: actual state/component marked K/E bridges and both marked diamonds.
- `bb86b82`: convex restriction and fixed-exterior actual core path lifting.
  The lift is injective, NOT a whole-component equivalence.
- `98f226c`: marked-E fibre signature by nonempty sizes, increasing fibre
  bijections, sink-order relabelings and closure invariance. P0/P2 complete.
- `0871d38`: restored crossing slide for `a<b<c<d`, replacing exactly `ab`
  by `cd` with only `ac,bd` covering initially. User-authorized Claude audit
  led to right-before-left restoration through the shared replay interface.
- `da01755`: ordered corner-chain preparation by actual flips, retaining
  already-good edges, component, total selected count and weak blocks.
- `03c05c4`: P3 complete. Auxiliary short-edge/copy geometry, neighboring and
  arbitrary parallel exchanges, and anchor connectivity at equal occupancies.
  Exact endpoint selection is `A-e+f`; every other edge is restored.
- `8fbbe84`: two-terminal-chain connectivity, forest extension to all feasible
  sizes, removable-edge avoidance, connected-position subset exchanges,
  subset bands and additive feasible-sector connectivity.

The sorted `chainPair` labels all non-retained auxiliary-path positions;
ordered `copyLabel` labels actual anchor copies. Do not conflate them.
Occupancy is NOT asserted invariant on a whole component. Equal occupancies
are a sufficient connectivity condition for anchors. No canonical highest
packing is claimed. Families may retain any maximal corners containing the
strict edges; specialize to `allCorners D` for the proof note's multigraph H.

P1 remains partial: other induced-core geometry and order reversal remain;
the specific nonconvex complete-interval lift is now proved. P4 remains
partial: the four five-vertex paths, final complete-diagram induction
assembly and reachability forcing remain. P5--P10 remain open. General component
recurrences, endpoint attachment and the final independent theorem are NOT
yet Lean-proved by this route. The mathematical diagram proof is complete.

### Verification and next step

Focused builds of `ChordConnectivityStep` and `CompleteSmall` and their
new dependencies pass without source warnings. All 244 queries in
`DiagramProofVerification.lean` pass using only `propext`, `Classical.choice`,
`Quot.sound` (or none). The independent import closure contains 147 project
files including the verification file and excludes the old word/scan/
expansion routes. Source guards, 100-column and whitespace checks pass.
Logs are `p4-chord-step-build.log`, `p4-small-build.log`,
`p4-chord-step-axioms.log` and `p4-chord-step-imports.txt` in the directory
below. No compiler or agent job remains running.

No broad build, dependency update, remote proof search or mathematical
computation ran. Only primary invokes `lake-workspace`. Lean MCP remains
rooted at RealRooted, so local compiler diagnostics are used. The wrapper's
existing package-path manifest warning remains unchanged.

Next: prove the four explicit five-vertex paths around line 3628 of
`COMPONENT_NN_REDISTRIBUTION.md`, using full selected sets at intermediate
steps as described above. Derive all equal-cardinality connections among
subsets of `{13,14,24}`. Combine that `n = 4` theorem with
`complete_reachable_of_le_three` and `complete_reachable_of_smaller` by strong
induction on `n`. Arbitrary component enumeration is not an assumption.
The optional later consolidation of the prefix/general restriction APIs is
recorded in `suggestions/complete-subdiagram-consolidation.md`.

The required independent Astra architecture review was completed before
implementation. Earlier verification logs remain under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diagram-formalization/`.
`p3-packing-*` records 107 axiom checks/106 project files;
`p4-helpers-*` records 120 axiom checks/111 project files;
`p4-prefix-*` records 148 axiom checks/121 project files;
`p4-chain-*` records 164 axiom checks/124 project files;
`p4-interval-*` records 195 axiom checks/131 project files;
`p4-rearrangement-*` records 222 axiom checks/138 project files;
`p4-outer-*` records 234 axiom checks/141 project files.

## Detailed formalization plan — completed before implementation

The user requested a detailed formalization plan after cleanup checkpoint
`61ff6f8`. The checkout was clean at that HEAD. Read the
[detailed plan](docs/COMPONENT_DIAGRAM_FORMALIZATION_PLAN.md): exact semantic
target, existing source interfaces, proposed modules, theorem obligations,
P0--P10 checkpoints, dependencies, acceptance criteria and focused checks.
At that planning checkpoint, all new Lean checkpoints were unimplemented.
The active implementation status above supersedes that historical status.
The mathematical proof remains complete.

Reuse `Circular.Diagram` with forwardness and actual orientations/flips/
components, keeping vertex-count path induction separate from the final
valuation induction. The review identified necessary small extractions from
`ComponentScalars` and `ForwardHRV` to keep the new imports independent of
word machinery. Component partitioning should also avoid importing
`ComponentCoefficient`. Marked E uses a fibre-coloring relation, not a new
natural diagram. Reduction terms are whole components on the same vertex
set, with common integer coefficients, forwardness and strict decrease.

Independent Astra reviewer `diagram_audit` approved the detailed architecture
after two ordering clarifications: auxiliary short-edge/copy-order geometry
is proved in P3 before the two-chain base; local target-decrease lemmas are
proved in P8 before reduction certificates and reused by P9. Its review
also covers endpoint semantics, corner validity, core lifting and component
multiplicities. It owns no files and is finished.

Primary owns the plan and this handoff. Only these two documentation files
change in the planning checkpoint. Source/interface/import inspection,
27 plan links and `git diff --check` pass. Existing proof notes and Lean
sources are unchanged. No builds or mathematical experiments ran; Lean MCP
is still rooted at RealRooted and was not used. No verification jobs remain.
At implementation start, recheck shared build ownership and begin P0/P1;
the plan proposes early crossing-slide and marked-semantics checks before
the longer path inductions.

## Cleanup audit before formalization — complete

The user requested one cleanup/optimization audit of the completed diagram
proof before Lean formalization. Starting HEAD is `8ccde0e`; the checkout
was clean. Read the [audit and extracted lemmas](docs/proofs/COMPONENT_DIAGRAM_AUDIT.md)
alongside the [assembled proof](docs/proofs/COMPONENT_DIAGRAM_COMPLETION.md).

The mathematical conclusion remains complete. The audit found no gap in
the reviewed completion argument. The assembled proof now chooses its
initial-path/first-block prefix directly from the area sequence: internal
v is an articulation iff a_(v+1)=1. This avoids general block-decomposition
infrastructure for the final recurrence. We also state the required
re-marking before alternating deletion and distinguish total selected-edge
layers from the original normal-edge exponent.

The audit note extracts proved finite forest-extension and subset-band
lemmas, the area-prefix lemma, component isolation by subtraction, and
attachment from a right-marked equality. It records the proposed two-stage
formalization (vertex-count path induction, then valuation induction),
existing Lean interfaces and import-boundary cautions. These are paper
lemmas and implementation guidance; no new Lean formalization is claimed.

Primary owns this handoff, the assembled completion, the new audit note,
and `suggestions/diagram-proof-import-boundary.md`. Existing chronological
proof-note prefixes remain unchanged. Independent Astra reviewer
`diagram_audit` owns no files; it reviewed recurrence, attachment, first-drop
and induction interfaces and approved the final cleanup and extracted lemmas.
This supplies the independent decomposition review required by the project
guide. Primary audited the path-induction side. No builds or mathematical
computations ran; no finite-check replay is claimed for this documentation
audit. Formalization remains the next implementation task.

Final cleanup checks: independent review approved the edited proof and
extracted statements; 21 local links and six Lean file breadcrumbs resolve;
the NN, DN, endpoint and coverage historical files are byte-for-byte
unchanged from `8ccde0e`; `git diff --check` passes. Only the four owned
documentation files listed above enter this checkpoint on `main`.
The reviewer is finished and no verification/build jobs remain running.

## Completed — ordinary component expansion by diagram recurrences

The mathematical goal is complete. The general first-drop NN and forward DN
recurrences now collect whole components with the same signed coefficients
for K and E. DD/ND inherit the same whole component by the proved unmarking
step. The resulting decreasing induction proves the general component
e-expansion for ordinary, non-circular Motzkin/Dyck-path diagrams.

Read the [assembled proof](docs/proofs/COMPONENT_DIAGRAM_COMPLETION.md).
It is independent of the separate word-functional proof and uses no
fundamental-basis calculation. This is a mathematical proof; no new Lean
formalization is claimed. The next requested step is preparation for
formalization through the cleanup audit recorded above.

### What closes the last gap

The new [initial-vertex inheritance](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#initial-vertex-inheritance-through-extra-edge-sectors)
applies when the first corner tails are 0,1. Delete vertex 0. The core loses
exactly the first corner and all remaining chain terminals stay unchanged.
A prepared source state is a core anchor, the retained corner 0a, and a
subset of good extra edges 0v. Each extra has a matching good core edge
ah_v. Their proved crossing slide restores arbitrary exterior.

First slide extras into the core until it is connected. For a fixed extra
set S, all same-size core anchors connect by the smaller-core theorem;
core flips lift because no forward core path can visit 0. Neighboring
extra sets connect by a crossing slide through a core witness omitting
its matching edge. Such witnesses exist when that edge can be removed
from the full good core without disconnecting it. The feasible extra
sets form a connected band of subset sizes.

This supplies a decreasing vertex-count induction for EVERY connected
ordinary natural graph without articulation. If the second corner tail
is greater than 1, use order-dual last-clique inheritance to remove the
initial private vertices. Otherwise use initial-vertex inheritance. Both
cores have fewer vertices and no articulation. Outside the complete and
two-chain bases, the good core quotient has at least three vertices and
no articulation, hence no bridge: every matching edge is removable.

Arbitrary initial paths preserve uniqueness by forced pendant deletion.
For a general connected non-path source, take the prefix consisting of
the initial path and first nontrivial block. It has the required uniqueness.
Use its right-marked full-layer recurrence and attach the arbitrary whole
component to its right. All products are whole; no expansion for the
attachment is assumed. Its first-drop contact is the full source's first
drop. Thus articulations do not require false global uniqueness at a
fixed total edge count or an unproved two-end attachment assertion.

### Whole-component recurrence and final theorem

For the unique connected common-cover component C in prefix layer k,
complete that source layer. Every extra source component reduces
independently by an absent corner, weak-block reordering, or alternating
corner deletion. Subtract these smaller expressions from the full-layer
NN or DN identity. All targets and correction terms are whole components.
The same integer coefficients work for K and E.

The first-drop coverage theorem and DD/ND inheritance supply the contact;
every final output decreases (n, natural area, area moment). Saturated
paths and disjoint natural components give the bases/factorization.
Consequently K(C)=sum_(A in C) e_lambda(A) for every ordinary component,
and restoring its constant normal-edge weight gives t^k(C) times this sum.

The construction chooses the required first-drop contact. It does not
claim a one-to-one correspondence of source and target components, nor
that the uncorrected local image is already a union of whole components.
Those stronger assertions were never needed and earlier counterexamples
remain valid. All former general NN/DN, higher-clique and three-corner
open statuses in the chronological notes are superseded by this proof.

## Verified evidence

All four final source-identical replays passed with exit 0 and empty stderr.
Frozen sources, commands, logs and hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/general-diagram-completion-20260930/`.

- Structural audit: all 6916 connected ordinary diagrams on 3..10 vertices,
  including all 2055 without articulation. The decreasing branches are
  8 complete, 618 initial-clique trims, 7 small-chain bases and 1422
  initial-vertex cases. All 6908 non-path prefix/first-drop choices pass.
  Also 1308 actual crossing slides, 6238 flips, up to four extras.
- Initial-vertex audit: all 37 applicable diagrams through seven vertices,
  plus the fourth power of an eight-vertex path (three extras). All 13474
  connected anchors, 1427 core joins / 3944 flips, 200 sector bands and
  214 sector links / 902 flips pass. Exact lift comparison covers 344211
  states and 1420896 directed actual-flip incidences, including states
  where other retained corners are redundant.
- General first-drop audit: 41 feasible layers in seven fixtures, covering
  NN, DN, ND-to-NN, DD-to-DN, three-/four-corner sources and an initial
  path prefix. 20274 survivor states; 2089 whole targets / 42054 states;
  275 block corrections / 1943 states; 948 absent-corner corrections /
  18051 states; 287 alternating sources / 1786 states, giving 6967 whole
  deletion terms. Signed marked HRV identities, whole-output and strict
  induction-order checks pass (5429 positive terms, 4850 negative terms,
  24358 redundancy witnesses).
- Right-attachment audit: all six initial-prefix layers with the two-state
  triangle attached to every term. All 3555 product-component checks pass,
  with 46844 product state visits and exact endpoint fibre data.

These are checks of the stated finite scopes. The unbounded proof is the
written path induction, sector argument, component correction and attachment
argument; it is not extrapolated from enumeration. No computational coloring
identity or basis calculation is claimed. Both K and E identities follow
from the proved common local diagrams and marked maps.

The existing 20000-state component guard is unchanged. Cargo runs were
serialized and reduced-priority; no Lean/Lake build ran. The maintained
Rust workspace is clean and unchanged at
`24559ad73d209077a58eef08278c425301468cdc`. The external consumer reuses the
existing Graph/Poset, actual-flip, crossing-slide and component-correction
APIs. Python only handled files, commands and diagnostic log summaries.

## Ownership, scope and recovery

Primary owns this handoff, `docs/proofs/COMPONENT_DIAGRAM_COMPLETION.md`, the
recurrence outline, APPEND-ONLY continuations of NN redistribution and DN
joint-repair notes, the authorized endpoint/source-addition continuations,
handoff archives and existing external consumers under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/`.
Preserve other ownership and the proof-note prefixes at `a3d076b`.

The original completion used no extra worker/subagent/Claude consultation,
manuscript TeX/PDF/Overleaf edit, maintained Rust edit or Lean build. The
subsequent cleanup's read-only review is recorded above. No account/profile/model
assignment changed. Runtime tools, `codex mcp list`, Cargo metadata, the
Rust guide and relevant existing APIs were inspected. Lean MCP remains rooted
at RealRooted and was unused. There is no external blocker or unfinished
requirement of this mathematical goal.

The [previous handoff](docs/archive/component-handoff-before-general-completion-20260930.md)
preserves `49cb610` with relative links relocated. All earlier proofs and
counterexamples remain intact. The outline now routes to the assembled
completion; dated notes, including the former conditional coverage theorem,
retain their historical wording and should be read with that completion.
The new proof discharges the coverage theorem's explicit NN/DN hypothesis.

The replacement began at account-swap `2511182`. Recent proof checkpoints
were `cf5451e` (pendant inheritance) and `d7da9ab` (last-clique inheritance),
followed by metadata `49cb610`. Completion proof checkpoint `a3d076b` is
committed and pushed to `origin/main`. All four frozen replays, receipt
hashes, preserved prefixes, historical outline body, relocated archive,
new file/heading links, ownership and whitespace checks pass. No verification
jobs remain running. The completion audit verifies the full ordinary scope,
whole smaller outputs, both valuations, well-founded induction and shifted
elementary positivity; no required work remains on this mathematical goal.
