# Complete-diagram implementation history

Archived from `HANDOFF.md` after pushed `eb3fa06`, when the remaining
five-vertex base and final induction were completed in the next checkpoint.
The statuses below are chronological; the current handoff supersedes them.

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

