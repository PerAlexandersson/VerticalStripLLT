# Earlier unicyclic swap and block checkpoints

Archived at the leftmost NN checkpoint. Open claims below describe their
then-current scope; see the current handoff for later proofs.

## Current leaf-envelope continuation

Continuation from clean pushed `5ddde49`; previous goal turn made proof
and evidence progress. Primary owns notes/handoff and external consumers,
retaining the sole Lean build slot. Existing Astra simpler_component_route
has a read-only task on first mixed NN joins. A tool-free Claude consultation
on uniform leaf-envelope restoration is authorized and monitored under a
20-minute timeout (native session 93566); receipts are in the external
`leaf-envelope/` directory.
No new workers/accounts, delegated edits, Lean build or manuscript change.
The full recurrence/diamond component proof remains the active goal.

## Current unicyclic block checkpoint

2026-09-28, continuation from clean pushed `cd29b7a`. The preceding goal
turn made proved progress. This increment adds a structural lemma, a
checked local repair, and exhaustive evidence; it does not complete the
requested general recurrence/diamond proof.

New [unicyclic block note](../proofs/COMPONENT_UNICYCLIC_BLOCKS.md):
contracting strict chains in an articulation-free ordinary natural graph
creates no loops or articulation. Deleting one chain leaves consecutive
labels at distance at most two, hence connected. The two-vertex multigraph
case has parallel edges and is handled explicitly.

The stronger uniqueness question remains open: is there at most one
surviving connected unicyclic component in each natural block? Exact search
passes every articulation-free saturated diagram on7 and8 vertices:
42/132 graphs,59881/1280832 connected selected states, one survivor per graph.
All survivors also contain a leaf-at-0 state with the full remaining
natural envelope. These finite assertions do not prove either uniform claim.
The known two-K4 articulation counterexample excludes unrestricted uniqueness.

Two precise obstructions guide the next proof attempt. Contracting the
smallest cycle vertex can create a redundant strict edge before reaching
a triangle. Also the tree envelope-augmentation sweep can make its retained
corner redundant halfway through. A five-flip repair fixes the smallest
K5 example and restores the smaller envelope. Primary and existing Astra
independently audited the lemma, examples, repair and final written note.
A full-envelope smaller component may still be inactive (explicit n4
example), so an induction must retain its correction rather than discard it.

Frozen sources/model, Cargo files, commands, receipts and18 hashes:
`/lake-cache/ai-projects/requests/VerticalStripLLT/unicyclic-blocks/`.
Final n7/n8 scans and repair finished exit0. An initial n8 run reached its
200000-state BFS cap only at K8; a bounded1m-cap rerun completed it and the
final full scan. A compile-only reference-pattern typo was fixed before
leaf-test execution. Historical logs are labeled; neither error is a
mathematical counterexample. Documentation links, hashes and diff checks pass.

Primary owns notes/index/handoff and the external consumer; sole serialized
Lean build slot retained. Astra's bounded read-only assignments are finished,
and all owned processes are terminal. No new workers/accounts, Claude call,
Lean build, manuscript edit or maintained Rust edit. Runtime/MCP and Rust
capabilities refreshed; Lean MCP still targets RealRooted and was unused.
Existing flip-enumeration API integration proposal remains.

Next: find a uniform repair that restores the smaller envelope after corner
leaf normalization, or close the remaining first/middle NN joins directly.
The unicyclic block evidence is a possible isolation route, not a replacement
for the full goal: higher cycle ranks, DN/DD and recurrence coverage remain.

## Current unicyclic swap checkpoint

2026-09-28, continuation from clean pushed `47a9c13`. This goal turn made
proved progress. The full recurrence/diamond component proof remains open;
the completed Lean word proof is not a substitute for the requested route.

[The four-cycle note](../proofs/COMPONENT_FOUR_CYCLE_SWAP.md) now proves
both LEFT and RIGHT second mixed NN joins stay in one connected unicyclic
source component. The left proof converts to the right core by two flips,
uses the earlier strict-corner attachment transfer, and undoes the temporary
moves. Arbitrary attached trees and all original strict corners are retained.

New general theorem: if a connected unicyclic state contains f=ac,r=bc,
omits q=ab, and its cycle contains either f or r, it is connected by actual
flips to its full adjacent-swap image. Delete f (or first swap if needed).
The tree envelope has r maximal; adjoining q to its maximal chains is a
forest. Normalize toward a tree containing q, stop before its first
introduction, apply the resulting four-cycle swap, and reverse the swapped
prefix. This avoids normalizing any q-containing state by conjugation.

Every nonactual middle join has a σ-invariant 01 endpoint. This does NOT
connect it to the 10 endpoint. A first mixed join still has an additional
ad/bd or ta/tb attachment discrepancy after the swap; the note displays it.
Middle/first mixed joins between surviving components, skipped-b inactive-f
neighbor uniqueness across q=0 pieces, higher cycle ranks, DN/DD isolation,
and full recurrence coverage remain open. No manuscript replacement.

Checks: left theorem on 24 states in all 76 eligible NN instances through
n=6, plus 47 and 5 in two n=7 fixtures; two explicit conversion tables.
General theorem with f on the cycle on 519 states in the same scan, plus
257 and 72 in the fixtures. All are actual-component assertions, not
polynomial comparisons. Every final Rust command finished exit 0.
Historical manifest-path and missing-natural-edge lookup errors are retained
and identified separately; both were fixed before the successful scans.

Primary and existing Astra simpler_component_route audited the proofs and
final statements. The authorized tool-free Claude audit finished exit 0
(native session 40855) and confirmed the longer normal-form argument,
cover preservation and stopped-prefix conjugation. Primary's shorter
q-forcing argument received its own independent Astra review. No result
is attributed to a reviewer who did not inspect that version.

Frozen consumer/source model, Cargo files, commands, receipts, Claude outcome
and 29 hashes: `/lake-cache/ai-projects/requests/VerticalStripLLT/left-four-cycle/`.
Primary owns the proof notes, docs index, handoff/archive and external
consumer, and retains the sole serialized Lean build slot. All bounded
agent assignments and owned processes are finished. No new worker/account,
Lean build, manuscript edit or maintained Rust edit. Existing flip API
integration proposal remains; Lean MCP still targets RealRooted and was unused.
Mathematical audits, finite assertions, documentation links, frozen receipt
hashes and `git diff --check` are the checks for this checkpoint.

