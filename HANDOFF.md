# VerticalStripLLT handoff

## Current continuation — right attachments and two overlapping cliques

Primary resumed from clean pushed `3dec58f`. The full general NN/DN goal
remains ACTIVE and UNFINISHED. Continue the author/Robin diagram method:
whole components, diamonds and justified relabeling. No fundamental basis
or substitution of the separate completed Lean proof.

**Proved this continuation:** every proved full-layer NN/DN recurrence
has a right-endpoint-marked version and therefore carries an arbitrary
right-hand attachment. Two path lemmas for overlapping cliques are also
proved; their full component recurrence is NOT yet proved.

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

**Unfinished next step:** reach the quotient star centered at F, then
rearrange the remaining selected positions in the two quotient cliques.
Their free-position sets share the extra FG copy. A detailed candidate
construction is preserved at the end of the NN note. Its proposed
connectivity assertions and restoration steps still need verification.
Do not infer full-layer uniqueness or a new recurrence from this plan.
The articulation case c=b has distinct product components; use the
right-attachment theorem instead of asserting layer uniqueness.

## Verification and receipt

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
Preserve other ownership and proof-note prefixes at `3dec58f`.

No Lean/Lake build, extra worker/subagent/Claude consultation, manuscript
TeX/PDF/Overleaf edit or maintained Rust edit is authorized in this lane.
Runtime registry, `codex mcp list`, Cargo metadata and relevant APIs have
been checked. The Rust guide was read in this continuation chain. Lean MCP
is rooted at RealRooted and unused. Maintained Rust remains clean at
`d53fb193af3c69adedbd9ec8592f87235d809ffa`. No worker/account/profile/model
assignment changed. No external blocker is present.

The replacement originally began at pushed account-swap `2511182`.
Previous proof checkpoint `c2fc099` and metadata checkpoint `3dec58f` are
pushed to origin/main. The new archive preserves the complete handoff at
`3dec58f`, with only relative Markdown links relocated.

All diagnostic jobs are complete. Proof-note prefixes, relocated archive,
local file links, receipt hashes and `git diff --check` pass before the
checkpoint. No process needs monitoring or restarting.
