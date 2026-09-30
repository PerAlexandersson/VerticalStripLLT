# VerticalStripLLT handoff

## Current continuation — all middle lengths in the three-corner DN family

Primary resumed from clean pushed `b7c4863`. The previous turn and this
continuation made verified progress. The full general NN/DN goal remains
ACTIVE and UNFINISHED. Continue the author/Robin diagram method: whole
components, diamonds and justified relabeling. No fundamental basis or
substitution of the separate completed Lean proof.

**New theorem:** [all middle lengths](docs/proofs/COMPONENT_DN_JOINT_REPAIRS.md#all-middle-lengths-in-the-three-corner-dn-family)
are proved for the DN sources with maximal corners

    {0a,1c,ae},       2<=a<c<e.

This removes the c=a+1 restriction of proof checkpoint `0884521`.
The source marks 0a and ae. If c=a+1, 1c must be unmarked; if c>a+1,
it may be marked or unmarked. Every source component has the same
signed recurrence for K and E, with whole smaller outputs. Right-marked
identities and arbitrary right attachments remain valid.

### The short proof

The corner chain beginning at 0 is {0,a,e}, with terminal e. After
preparation (P), every normal edge at 0 is absent: its chain label would
point downwards. Thus 0 is pendant on 0a. Delete it. The remaining natural
graph is exactly the two overlapping cliques [1,c] and [a,e], with
maximal corners 1c,ae. The prepared restriction is connected, has both
corners covering, and has one fewer edge.

The two-clique theorem connects all such restrictions of equal size.
Its paths lift with the pendant edge fixed, because a directed internal
cover test cannot visit 0. Reverse the preparations to connect the
original states. This proves common-cover component uniqueness. Then
independently reduce every extra source component by an absent corner,
weak blocks, or alternating corner deletion, and subtract from the full
DN layer identity. The outputs are whole by those correction theorems.

Pendant deletion alone is NOT a whole-component map. For instance,
{02,13,24,12} has 0 pendant, but its 012 flip gives {02,13,24,01}.
The lifted core subset has exits involving 0. We use it only to prove
paths/uniqueness, never as a value identity or a leaf-factor formula.

### General pendant inheritance

The [new path lemma](docs/proofs/COMPONENT_NN_REDISTRIBUTION.md#pendant-inheritance-of-common-cover-uniqueness)
applies when the first maximal corners are 0a,1b and every 0<v<a has
corner-chain terminal r(v)<r(0). Deleting 0 introduces no new maximal
corner; common-cover uniqueness in the smaller diagram implies it in
the original. The hypothesis holds if 0's chain ends at the last vertex.

Reverse only paths for the order-dual version. In particular, consecutive
last maximal heads and a last-vertex chain starting at 0 permit right
peeling in reversed preparation. This also proves the corresponding
three-corner family 0a,bc,ae with b<a<c=e-1. It does not assert order-
reversal invariance of K or E; use the original diagram's own recurrence.

## Verification and receipt

All three final frozen-source replays passed with exit 0 and empty stderr at
`/lake-cache/ai-projects/requests/VerticalStripLLT/dn-pendant-recurrences-20260930/`.
Verified checks:

- `--dn-pendant-lift`: all ten (n,a,c) choices on 5..7 vertices; 495
  connected anchors, 7176 visited core states, 23836 directed flip
  incidences. Every prepared restriction of a given size has one core
  component. Every core flip, including ones through redundant-corner
  states, is compared exactly with its source lift.
- The same mode with `--eight`, (n,a,c)=(8,3,5): 674 anchors, 21577 core
  states and 89252 incidences. Totals span several components and layers;
  the existing 20000-state limit per component remains unchanged.
- `--dn-pendant-layers --right-marked-layers`: all ten small diagrams,
  fourteen allowed marking choices, 58 feasible layers. 33786 survivor
  states, 3066 whole targets / 66236 states; 466 block corrections / 3709
  states; 2105 missing-corner corrections / 27459 states; 213 alternating
  sources / 1282 states, yielding 2467 whole deletion terms. 4193 positive
  and 3911 negative terms, 8974 redundancy witnesses. All signed marked
  fibre, whole-output and induction-order checks pass. The counts include
  the earlier minimum-middle controls.

A separate full-layer `--eight` attempt exited at the pre-existing
20000-state component guard during enumeration. It gives NO whole-layer
verification for that fixture. The guard was not increased, and that
attempt was not repeated. Its logs are retained separately; the successful
eight-vertex core-flip audit above is distinct. The general proof relies
on the two-clique theorem, not extrapolation from these bounded checks.

Only the existing external `dn_joint_span.rs` consumer changed, reusing
the established actual-flip and Graph APIs. Python is file/command
orchestration only. No new polynomial generator, coloring enumeration,
basis calculation, Lean build or maintained Rust edit ran.

## Remaining problem

General NN/DN component collection remains unproved beyond the established
families and their valid attachments. The larger-middle family previously
listed as open is now solved; do not keep it on the open list.

Pendant preparation is not enough if deleting the extreme vertex introduces
a new maximal corner that need not be selected or covering. For example,
with three corners 0a,bc,ae and b>1, deleting 0 introduces 1a. When also
c<e-1, the stated right-peeling criterion does not resolve this geometry
either. Other three-clique NN geometries and general higher-clique sources
still need a proof. Do not infer uniqueness simply from connectedness or
from finite generator checks.

The earlier six-fixture three-clique generator audit remains useful:
packing and connected two-clique-region replacements alone miss some
anchors; adding connected-clique-piece moves connects its finite layers.
This is not a general generation theorem. Direct RHS diamond redistribution
remains an alternative to proving global common-cover uniqueness.

## Established results and history

The [previous handoff](docs/archive/component-handoff-before-pendant-dn-20260930.md)
preserves the full state at `b7c4863`, with only relative links relocated.
It retains the explicit two-side DN proof for c=a+1 and its 4548 checked
paths. The pendant argument is a shorter extension; those earlier results
remain valid.

Also retain right-marked attachment recurrences, two-overlapping-clique NN
recurrences, terminal-clique and order-dual families (all ordinary path
powers), three-chain families, DD/ND inheritance, first-drop induction,
fixed-short reductions, arbitrary trees, maximum common-cover layers,
complete diagrams, the stated cubes and prior fixed examples.
Preparation (P), arbitrary crossing slides, canonical packing and connected
pieces in selected-cover intervals remain available with their hypotheses.

Unrestricted adjacent-swap active membership is false already in K5 with
strict 04. Keep its counterexample. A local path establishes membership,
not a state's K/E equality; canonical anchors cannot replace whole sums.

## Ownership and recovery

Primary owns this handoff, the recurrence outline, APPEND-ONLY continuations
of the NN redistribution and DN joint-repair notes, earlier authorized
endpoint/source-addition continuations, handoff archives and existing external
consumers under
`/lake-cache/ai-projects/requests/VerticalStripLLT/diamond-exploration/hrv-bridge/`.
Preserve other ownership and proof-note prefixes at `cf5451e`.

No Lean/Lake build, extra worker/subagent/Claude consultation, manuscript
TeX/PDF/Overleaf edit or maintained Rust edit is authorized in this lane.
The runtime registry, `codex mcp list`, Cargo metadata, Rust library guide
and relevant existing consumer/API code were checked. Lean MCP is rooted
at RealRooted and unused. Maintained Rust is clean at
`24559ad73d209077a58eef08278c425301468cdc`; the receipt checks the revision
before and after its replays. No worker/account/profile/model assignment
changed. No external blocker is present.

The replacement began at pushed account-swap `2511182`. Recent pushed
proof checkpoints are `4beccde` (right attachments), `8149366` (two cliques)
and `0884521` (minimum-middle DN), followed by metadata `b7c4863`.
Proof checkpoint `cf5451e` (pendant inheritance and arbitrary middle DN)
is committed and pushed to `origin/main`.
Frozen receipt hashes, preserved proof-note prefixes, archive relocation,
relative file links and whitespace checks pass. No verification jobs remain
running. The full general goal is not complete.
