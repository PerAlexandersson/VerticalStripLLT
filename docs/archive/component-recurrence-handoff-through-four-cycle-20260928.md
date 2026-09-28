# Component recurrence checkpoints through the right four-cycle

## Current four-cycle attachment checkpoint

2026-09-28, continuation from clean pushed `37e813a`. Previous goal turn
made proved progress. The full recurrence/diamond proof remains open;
the new theorem resolves one complete NN generator in cycle rank one.

New [four-cycle swap theorem](../proofs/COMPONENT_FOUR_CYCLE_SWAP.md):
for eligible saturated ordinary NN a<b=a+1<c, any connected unicyclic
state containing {ac,ad,bd,bc}, b<d<c, is connected by actual flips to
its adjacent-swap image, with arbitrary attached trees. This proves the
RIGHT second mixed NN join stays in one source component.

Proof ingredients: a six-flip incoming-attachment transfer using a strict
corner in another branch; seven flips move the interior cycle vertex along
an attached edge. A new [tree interval-path lemma](../proofs/COMPONENT_TREE_CONNECTIVITY.md)
normalizes the containing corner's branch so its path to the core stays
inside the endpoint interval. Move the cycle along that path, transfer
the incoming branch, then undo migration and normalization. The moved
branch remains pendant and cannot alter the reversed cover tests.
Strict edges are retained. Same-branch shields use tree connectivity and
a conjugated return path. Primary and independent Astra audited the final
written proof and every local cover test, including empty-path cases.

Exact checks: six-/seven-flip tables; all 149 relevant unicyclic states in
all 76 eligible NN instances through n=6; another 44 and 13 states in
two n=7 fixtures. All adjacent-swap images lie in the same actual component.
A separate exact K5 counterexample shows that keeping a normal edge
redundant throughout a tree-normalizing path is too strong, even for the
special pair and the same directed path. Do not use that rejected shortcut.

The unicyclic note also records two partial skipped-b reductions: q=1
paths lift under A→A−q+r, and first-mixed incidences correspond to actual
q-changing flips inside the inactive component. Comparing their exterior
swaps and propagating across whole q=0 excursions remain unproved.

Receipts, frozen sources/manifest/lock, commands and 17 hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/four-cycle-attachment/`.
All final jobs finished exit 0. Primary owns notes/index/handoff and
external consumer, retaining the sole Lean build slot. Existing Astra
simpler_component_route supplied independent proofs/audits and the precise
restricted-tree obstruction; all bounded assignments are finished.
Independent proof audit, exact checks, frozen hashes, local documentation
links and `git diff --check` pass. No delegated edits or owned live processes.
No new worker/account, Claude
call, Lean build, manuscript edit or maintained Rust source edit.
Runtime/MCP and Rust capabilities refreshed; Lean MCP still targets the
other project. Existing flip-enumeration integration proposal remains.

Next: LEFT second mixed NN join; middle/first-mixed joins between surviving
components; skipped-b inactive-f neighbor uniqueness including q=0 pieces.
Higher cycle ranks, DN/DD isolation, and recurrence coverage remain part of
the full goal. The completed word proof is not a substitute for this task.

## Current unicyclic packet checkpoint

2026-09-28, continuation from clean pushed `148cc9c`; previous goal turn
made proved progress. The general recurrence/diamond component proof is
still incomplete. Keep the full goal active and preserve the manuscript.

New results in [the unicyclic note](../proofs/COMPONENT_UNICYCLIC_REDUNDANCY.md):

- A connected unicyclic component is wholly mixed-cyclic exactly when one
  strict corner is redundant throughout. A mixed directed cycle with two
  strict edges has an actual flip breaking it; the no-switch lemma handles
  the one-strict-edge case. Thus all discarded components are classified
  by insertion into whole tree components with a forced maximal chain.
- Across NN joins, inactivity at g different from the distinguished corner
  f is preserved. The forced chain avoids the adjacent vertices a,b and
  remains maximal under the swap. LEFT mixed joins also change ta outside
  f; the common selected long tb shields it. This detail is incorporated
  following the independent audit. Such vertices cannot lead to a survivor.
- An inactive-f bypass a→b→c gives an isolated packet vertex. A longer
  bypass through b gives exactly one neighboring component, which survives.
  The entire middle image is connected by lifted actual flips.
- A nine-vertex exact example joins DISTINCT inactive-g components (g≠f).
  Different deletion envelopes prove they are different whole components.
  Do not strengthen label preservation to equality of components.

Exact scan: all 76 eligible NN instances through n=6, 99 connected
unicyclic component occurrences (22 surviving, 77 inactive). The common
strict-corner classification and proved NN predicates pass. Distinguished
inactive bypass counts: 27 skip b, 22 have length two through b, 19 are
longer through b. All 46 distinct intercomponent joins in this bounded
scan go from inactive-f to surviving; this is NOT a uniform theorem.
The two n=7 fixtures pass too. The n=9 example is checked locally,
without enumerating its entire state space; the structural tree theorem
supplies the whole-component and distinctness conclusions.

Frozen sources, manifest/lock, receipts/logs, commands and 13 hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/unicyclic-packet/`.
All final jobs finished exit 0. Primary owns the notes/index/handoff and
external consumer, retaining the sole Lean build slot. Existing Astra
simpler_component_route supplied the classification and through-b cases,
audited the other-corner proof, and independently checked the n=9 example.
All bounded assignments are finished, no delegated edits or live jobs.
Independent mathematical audit, exact assertions, frozen-file hashes,
relative documentation links and `git diff --check` pass.
No new worker/account, Claude call, Lean build, manuscript edit or shared
Rust source edit. Registry/MCP and Rust capabilities refreshed; Lean MCP
still targets RealRooted. Existing flip-enumeration API proposal remains.

Next: control the inactive-f forced chain that skips b, and prove source
connectivity for surviving-to-surviving joins. A right second mixed join
contains an alternating four-cycle with attached exterior trees; outgoing
branches can be swapped by two actual flips. Incoming branches can be
shielded by a strict edge in a DIFFERENT branch, so tree connectivity
inside one branch does not prove the general swap. Higher cycle ranks,
DN/DD isolation and complete recurrence coverage remain necessary too.

## Current global-reassembly checkpoint

2026-09-28, continuation from clean pushed `246345c`. The requested general
recurrence/diamond component proof is still incomplete; the earlier full
Lean word/finite-companion proof remains complete. Keep the research goal
active. No manuscript or Lean theorem has been replaced by this partial route.

New [whole-component correction](../proofs/COMPONENT_GLOBAL_REASSEMBLY.md):
for NN at 26 in area (0,1,2,3,4,3,4), strict corners 04,26, the remaining 1693-state component
has a packet consisting of itself plus an inactive 89-state component.
The packet transports to 26 whole smaller components, total 1,782 states;
deleting 26 from the correction gives one whole 89-state tree component.
Thus this particular source component has the same signed recurrence for
K/E. Finite packet identification is exhaustive, not a general theorem.
All 1,405 source components give 703 packets; each has at most one of the six
remaining components. All 55,232 directed target flips preserve packet weights.

New uniform theorem in [tree connectivity](../proofs/COMPONENT_TREE_CONNECTIVITY.md):
reachability common to all trees with envelope H is exactly Reach(M), where
M is its maximal intervals. Contract the increasing chains of M, prove the
quotient strongly connected, and extend a reverse quotient path to a tree.
It characterizes inactive strict-corner insertions into tree components.
Primary and independent Astra audited both proofs; exact enumeration agrees
for 1,441 trees in 64 whole components, n=2..6.

The same 1,693-state example disproves endpoint-only redundant-edge repair:
the canonical NN weights differ across an actual flip between two TREES.
Both selected-edge lists and the safe whole-component correction are in
the note. Do not infer that every bad boundary has a redundant endpoint.

Receipts, frozen source/manifest/lock, reproduction commands and 20 hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/global-reassembly/`.
All mathematical computation jobs finished exit 0, including the final
26-target-list and 89-state deletion check. No new polynomial family or
maintained Rust edit; existing flip API integration proposal remains.

Primary owns notes/index/handoff/external consumers and sole Lean build slot.
Existing Astra simpler_component_route worked read-only/build-free and its
bounded final audit is complete. No delegated edits or active Rust jobs.
The authorized read-only Claude global-construction consultation reached
its 20-minute timeout (exit 124, session 75994 terminal), without final text
or a result record. No Claude proof or audit conclusion is adopted. Request,
stream and status are retained externally. No account/model override or new worker.
Registry/MCP and Rust capability checks refreshed. No Lean build occurred.
All owned processes are terminal; exact Claude PIDs and descendants are absent.
Independent proof audit, frozen receipt hashes, documentation links and
`git diff --check` pass.

Next: prove general whole-component reconstruction. The remaining packet question is whether
paths through solved source components can join two distinct surviving
components. The new tree theorem does not establish that isolation claim.

