# VerticalStripLLT handoff

## Current continuation — right attachments and two overlapping cliques

Primary resumed from clean pushed `3dec58f`; right-attachment checkpoint
`4beccde` is pushed. The subsequent two-clique argument is now complete. The full general NN/DN goal
remains ACTIVE and UNFINISHED. Continue the author/Robin diagram method:
whole components, diamonds and justified relabeling. No fundamental basis
or substitution of the separate completed Lean proof.

**Proved this continuation:** every proved full-layer NN/DN recurrence
has a right-endpoint-marked version and therefore carries an arbitrary
right-hand attachment. The full component NN recurrence for arbitrary two overlapping natural
cliques is now also proved. This does not settle general NN/DN collection.

### Right attachments

The [right-marked theorem](docs/proofs/COMPONENT_RECURRENCE_ENDPOINT_EXTENSION.md#full-layer-recurrences-preserve-the-right-endpoint)
keeps the largest vertex c at a fixed color. Its HRV expression depends
only on the size of c's fibre and the other fibre sizes. Diamonds,
contact swaps, missing-corner and redundant/alternating deletions preserve
this mark. For a disconnected correction, put c's weak block LAST and
order each block increasingly. This fixes c, gives the same whole-component
isomorphism, and still strictly decreases natural area.

Consequently all proved full-layer families (complete, terminal-clique
and order-dual, three-chain, tree and maximum-layer) have the marked
recurrence. Gluing any whole component at c gives the same signed
recurrence of whole product components; no expansion for the attachment
is assumed. An outer right mark may be retained. Arbitrary two-end
attachments still require both endpoint marks to be preserved.

### Two overlapping cliques

For natural cliques [0,b] and [c,d], 0<c<b<d, the maximal corners are
f=0b and g=cd. The corner chains F={0,b}, G={c,d} give two quotient
cliques sharing F,G and the overlap singletons. Only FG has two good
copies, 0c and bd. See the [detailed continuation](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#two-overlapping-cliques-two-proved-path-lemmas).

Two path lemmas are proved:

- Every connected anchor reaches an anchor containing the shared FG class.
  If both copies are absent, sweep incoming d-edges across g to make d
  pendant (0 already is). Force c to reach b in the remaining connected
  graph. Sweep its reachable incoming b-tails across f in decreasing order,
  then walk the new 0-edge backwards along a c-to-tail cover path to 0c.
  Preparation (P) retains this already-good edge.
- A connected restriction to U={0,...,b} union {d} can be replaced by any
  connected anchor of equal size on U, restoring all exterior edges.
  Sweep vd to cv for b<v<d in decreasing order. No exterior path can
  return to U. The core is order-dual terminal-clique, so its proved
  local path lifts. At the endpoint c has only cd internally; undo the
  sweep in increasing order. This is a path lemma, not a K/E state identity.

**Completed next step:** [two-clique component theorem](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#complete-component-recurrences-for-two-overlapping-cliques).
Every connected anchor reaches the quotient star centered at F, represented
by 0b,cd and all bv with 1<=v<=d, v not in {b,c}. To obtain it:

1. Select bd using the shared-class lemma and crossing transport. In the
   right block containing cd, use the complete-cover theorem to select its
   terminal star at b. In every other right block, connect its intersection
   with [c+1,b] by the reachability construction. Hull steps above b do not
   remove internal overlap edges; later internal flips preserve weak blocks.
2. Move bd to 0c if needed. Every right block now meets just one selected
   left component, so global connectedness forces the left restriction
   connected. Normalize it with retained 0b to its good tree with 0c and
   all ib, i!=c, plus enough extra good edges.
3. Restore bd if necessary. The right restriction is connected via the
   overlap star and cd,bd. Normalize the entire right clique to its terminal
   star at b. Left-exclusive edges stay fixed.

The remaining free positions are the nonstar classes plus the extra FG
copy 0c. Their left-core and right-clique sets cover all positions and
share 0c. The core-isolation lemma gives arbitrary equal-count changes
on the left. The earlier arbitrary-capacity terminal transfer proof gives
those on the right (FG capacity two, other capacities one); its only
outside copy is 0c, moved by the established crossing transport. A swap
between sides uses 0c as an intermediate, in the appropriate order
according as it is absent or present. Its original status is restored.
Thus all connected common-cover states of fixed size are in one actual
component retaining both corners.

Every other source component reduces independently by an absent corner,
weak blocks, or alternating corner deletion. Full-layer subtraction gives
the desired NN recurrence of whole smaller components. It also has a
right-marked form and arbitrary right attachments. Two crossing maximal
corners are not a direct DN source with touching strict corners; this
result must not be reported as solving all DN cases. The articulation
case c=b has distinct product components, covered by the endpoint theorem.

**Still open:** general NN/DN component collection for more complicated
clique overlaps. A next question is whether a connected core can be
isolated and its exterior restored across a third clique, with enough
shared good positions to transfer edge counts. Do not assume such a
core-isolation or global uniqueness statement without proof.

## Verification and receipts

All three final frozen-source replays passed serially, with empty stderr.
Receipt:
`/lake-cache/ai-projects/requests/VerticalStripLLT/right-marked-attachments-20260930/`.
The final checks give:

- 14 complete-source NN layers: exact signed right-marked fibre data.
- 19 terminal-clique NN/DN layers: the same marked identity, all whole
  target and correction checks, and the endpoint-fixed block permutation.
- Attach a two-state triangle at the right of every source and final
  output in the complete checks: 2722 whole products, 63544 state visits.
  Every state has the predicted merged HRV fibres. Products are checked
  with actual-flip BFS, including closure.
- `--two-clique-bridge`: all 84 two-clique parameter choices on 4..10
  vertices; exhaustive anchors through six, 128 deterministic samples
  per larger graph. 1870 applicable anchors, 14534 actual flips, maximum
  path length 24, up to 44 natural edges. This checks introduction of FG;
  core isolation is proved on paper, not exercised by this mode.

Both two-clique final frozen-source replays passed serially at
`/lake-cache/ai-projects/requests/VerticalStripLLT/two-clique-recurrences-20260930/`.
Both exited zero with empty stderr:

- `--two-clique-star`: all 84 parameter choices on 4..10 vertices,
  exhaustive connected anchors through six, 128 samples per larger graph.
  8129 paths, 3382342 actual flips, maximum path length 3190, up to 44
  natural edges. Every endpoint is a good star anchor and all corners
  stay selected. The final extra-edge rearrangement is proved using the
  prior terminal-transfer theorem and core-isolation lemma; this mode
  checks star normalization, not that final rearrangement.
- `--two-clique-layers --right-marked-layers`: all 17 source layers in
  fixtures (n,b,c)=(6,3,2),(7,4,2),(7,4,3), at the first NN corner.
  25804 survivor states, 1773 whole targets / 38107 states; 676 weak-block
  corrections / 6003 states; 783 alternating source corrections / 6300
  states, yielding 3353 whole deletion terms. 3058 positive and 2744
  negative terms, 18900 redundancy witnesses. All signed marked fibre
  identities, output-component and smaller-diagram checks pass.

Only the existing external `dn_joint_span.rs` consumer changed. It reuses
the maintained ordinary HRV, Graph and Poset APIs and the existing actual
flip model. No new polynomial generator, coloring enumeration, basis
calculation, Lean build or maintained Rust edit ran. Python was used only
for file bookkeeping and serialized command orchestration. The 21-edge
full-enumeration and 20000-state component guards remain.

## Established results and open boundary

The [previous handoff](docs/archive/component-handoff-before-right-marked-20260930.md)
retains the complete terminal-clique proof and its receipt. In particular:

- Every terminal-clique family M={0h_0,...,ah_a}, strictly increasing heads
  and h_a=N-1, has complete eligible NN/DN recurrences. The order-dual
  family also does. This includes every ordinary path power with no
  divisibility or chain-count restriction.
- DD/ND inheritance, first-drop induction, all fixed-short reductions,
  arbitrary trees, maximum common-cover layers, three-chain families,
  complete diagrams, the stated cubes and earlier fixed examples remain
  proved. Preparation (P), arbitrary crossing slides and packing remain
  available with their exact hypotheses.
- The connected-piece lemma works inside ANY selected natural cover's
  interval, on its local connected block; the retained edge may be normal.
- Unrestricted adjacent-swap active membership is FALSE already in K5
  with strict 04. Its exact counterexample is in the NN note. The complete
  recurrence reduces that inactive output independently; do not reopen
  the false shortcut as an unsolved recurrence.

General NN/DN collection remains unproved beyond the established families
and their valid attachments. Local path lemmas establish membership;
canonical anchors cannot replace sums over whole components. The aim is
to isolate one source component in a signed sum of whole smaller outputs.

## Ownership and recovery

Primary owns this handoff, the recurrence outline, APPEND-ONLY continuations
of the NN redistribution and DN joint-repair notes, earlier authorized
endpoint/source-addition continuations, handoff archives and existing external
consumers under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/`.
Preserve other ownership and proof-note prefixes at `4beccde`.

No Lean/Lake build, extra worker/subagent/Claude consultation, manuscript
TeX/PDF/Overleaf edit or maintained Rust edit is authorized in this lane.
Runtime registry, `codex mcp list`, Cargo metadata and relevant APIs have
been checked. The Rust guide was read in this continuation chain. Lean MCP
is rooted at RealRooted and unused. Maintained Rust was initially clean at
`d53fb193af3c69adedbd9ec8592f87235d809ffa` and is now clean at
`24559ad73d209077a58eef08278c425301468cdc` after another worker added an
induced-P4 predicate and tests. The entire intervening diff was inspected:
it only adds unused Graph methods/tests and its handoff; none of the APIs
or source paths used by these checks changed. This lane made no Rust edit. No worker/account/profile/model
assignment changed. No external blocker is present.

The replacement originally began at pushed account-swap `2511182`.
Previous proof checkpoint `c2fc099` and metadata checkpoint `3dec58f` are
pushed to origin/main. The new archive preserves the complete handoff at
`3dec58f`, with only relative Markdown links relocated.

Right-attachment checkpoint `4beccde` is pushed. Both new frozen-source
replays, proof-note prefixes, local file links, receipt hashes and
`git diff --check` pass. All diagnostic jobs are complete; no process
needs monitoring or restarting. The general NN/DN goal remains active.
