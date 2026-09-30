# Diagram path implementation through `7d76087`

Archived from `HANDOFF.md` at the local complete-block checkpoint.
These entries are chronological; the current handoff supersedes their
remaining-work descriptions. No mathematical proof-note prefix was changed.

### Verified at `7d76087` — general reachability forcing

- `HassePaths` converts induced selected weak connections into simple
  Hasse paths within the same convex set. Graph paths are only auxiliary;
  the semantic weak relation remains `WeakReach` / `Relation.EqvGen`.
  `eqvGen_within_of_class_subset` also restricts a whole selected weak
  block to a containing set.
- `PathSplit` removes an internal vertex from a simple path and supplies
  its two distinct neighbors and remaining fragments. The fragments stay
  in the original support and avoid the removed vertex.
- `PathShortening.exists_weakReach_below` and `exists_weakReach_above`
  apply the prescribed incoming/outgoing cover flip at the upper/lower
  extreme. The remaining Hasse edges and the new short edge form a selected
  weak path in the strictly smaller interval. At most one actual flip is
  needed. All old selected edges with head below the removed maximum,
  respectively tail above the removed minimum, survive.
- `HullReduction` repeats upper and lower removal by strong induction,
  refining selected connections to Hasse paths at each step. Both the
  smaller interval and the relevant selected-edge preservation are proved.
- `ReachabilityForcing.exists_reachable_of_weakReach` combines hull
  shortening with the previously checked incoming normalization: for every
  forward ordinary diagram and every `u <= v` in one selected weak block,
  an actual-flip endpoint has a directed selected path from `u` to `v`.
  All strict edges remain selected by the actual orientation interface.
- `exists_selected_adjacent_of_weakReach` and
  `not_weakReach_of_adjacent_absent` give the stated adjacent-edge consequence.
- `exists_reachable_preserving_lower_weakReach` starts from the least vertex
  `u` of its selected weak block, with `v <= t`. It forces `u` to reach `v`
  and preserves every existing induced weak connection on `{x | x <= t}`.
  Upper-hull removal preserves the old selected edges there; subsequent
  normalization inside `[u,t]` preserves its induced weak blocks. The
  conclusion is only a forward implication for initial lower weak
  connections; equality of lower weak-block partitions is not claimed.

Terra's two independent read-only audits found no gap in path splitting,
source-cover geometry, exact edge retention, induction measures, ordinary
endpoint semantics or the lower-interval preservation claim. The full
reachability-forcing lemma is now verified. Its localization to a specified
clique/weak block with fixed exterior still belongs to the next interface.

### Verified at `7b9f5de` — reachability inside an interval

- `IncomingFlip.exists_reverseFlip_of_sourceCovers` supplies the incoming
  exchange as a reverse directed witness, with exact short-edge endpoints.
- `RestrictedFlips.DirectedFlipWithin` records that all three vertices of
  an actual directed flip lie in a specified set. Reverse paths of these
  flips are actual ambient flip paths. They fix every selected edge outside
  that induced set and preserve induced weak blocks in every containing set.
- `IncomingNormalization.exists_leftUnique_covers_within` repeatedly removes
  incoming cover forks inside the specified set. Each reverse flip strictly
  decreases `selectedTailSum`. Strict edges are retained by the actual
  orientation/flip interface. The global version is also proved.
- `UniqueIncomingPaths` proves that a left-unique relation gives common
  ancestors to weakly related vertices. Cover factorization then proves
  that a least vertex of a weak block reaches the whole block when incoming
  covers are unique. `eqvGen_relationCover_iff` extracts the reusable fact
  that replacing selected edges by cover paths preserves weak blocks.
- `IntervalReachability` proves exact convex restriction of paths and
  covers, including induced weak-block preservation under cover refinement.
  `exists_reachable_within_of_minimal` handles a least vertex of an induced
  weak block in any convex set. `exists_reachable_within_interval` specializes
  to a weak path already inside `[u,v]`, producing a state where `u` reaches
  `v` by actual flips confined to that interval.

Terra's independent audit found no gap in flip direction, termination,
preservation, minimality transport or interval semantics. These results
finish the normalization stage of the written reachability argument. The
current increment above supplies the formerly missing hull shortening.

### Verified at `c1e2e8e` — complete-diagram connectivity

- `CoverCut.relationCover_of_cut` gives a sufficient cover test: the selected
  edge is the only edge allowed to cross a separating set. Its proof uses
  forward path intervals and applies to arbitrary linearly ordered vertices.
- `FiveVertexPaths` interprets the four written triple lists as actual flip
  paths. Every intermediate state is built from its full selected endpoint
  set. Each step checks the two source covers through finite separating-set
  conditions, then uses the proved incoming/outgoing flip constructor.
  All finite conditions and exact final pair sets are kernel-checked with
  `decide`; no native proof axiom or component enumeration is used.
- `FiveVertexBase` identifies the three possible chords `13,14,24`, proves
  exact endpoint equality with the actual chain states, and combines the
  four paths. `ThreePositionPaths` supplies the abstract eight-subset and
  cardinality case split. Normalization yields `complete_reachable_five`.
- `CompleteConnectivity.complete_reachable` proves, for every `n`, that two
  selected-connected states in `completeDiagram n`, each covering `0n` and
  having the same total selected-edge count, connect by actual flips.
  Strong induction combines `n <= 3`, the explicit `n = 4` base, and the
  interval/chord step for `n >= 5`. There is no remaining smaller-diagram
  assumption in this theorem.
- `complete_reachable_marked` proves the corresponding path in
  `completeCornerDiagram n hn`. The corner `0n` is strict at every state.
  The endpoint active-cover hypotheses are retained; coverhood at every
  intermediate state is not claimed.

Terra independently audited the separating-set interpretation, full endpoint
identities, four finite paths, three-position assembly, strong induction and
marked transport. No gap was found. This completes the complete-clique
connectivity part of P4, not the general ordinary component expansion.

The [implementation history](diagram-complete-clique-implementation.md)
preserves the earlier CC1--CC6, interval and chord checkpoints, including the
corrected intermediate-state issue. Its former unfinished statuses are
superseded here. No earlier mathematical proof-note prefix was changed.

