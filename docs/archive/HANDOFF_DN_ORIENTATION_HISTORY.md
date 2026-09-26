# DN orientation integration history

Current alias-foundation checkpoint (2026-09-26): primary owns all source,
integration, documentation, remote requests, and the sole global build slot.
All Luna/Terra edit lanes are released; no build-slot transfer occurred.

New locally checked declarations:
- `Diagram.exists_aliasTarget_of_reverseBounce`: the actual overlapping ND
  search yields a valid diagram with the exact two-row update, unchanged
  strict count, and doubled half-square area smaller by six.
- `aliasTarget`, `aliasTarget_pairGraph_strictEdges`,
  `aliasTarget_doubledArea`: explicit constructor, strict relation, and measure.
- `PairGraph.coloringLLT_eraseNormal_forced` / `_descent` and
  `Diagram.shiftedOrientationExpansion_forced_edge` / `_descent_edge`:
  forced strict reachability removes a normal edge with the correct factor.
- `adjacentSwap_involutive`, `_translate`, `_threshold_iff`, `_strictMonoOn`:
  simultaneous disjoint periodic adjacent swaps for the overlap conjugacy.
These are foundations, not the full overlap polynomial identity. Exact proof
route: `docs/proofs/CIRCULAR_ND_ALIAS_REDUCTION.md`.

Default build passes (1786 jobs); 957 axiom checks pass with only propext,
Classical.choice, and Quot.sound. Source/100-column guards, initialization
ancestry, immutable-reference checks, and diff whitespace checks pass.
External logs: `circular-alias-foundation-build.log` and `-axioms.log`.
Current pushed checkpoint: `9561ad0` (alias foundations). Previous `82c1f81`
proved direct DN coloring and R1 area decreases.

New port ownership: Luna `circular_data` owns only new `Circular/HRVStepComparison.lean`,
`Circular/HRVTriangle.lean`, and `Circular/OrientationPairSum.lean`, extracting
and porting the generic DNWork helpers from the external Aristotle candidate.
All three Luna ports returned and primary adopted them; no build-slot transfer.
Primary owns all DN integration files and the global build slot.

Luna `circular_data` owns only new `Circular/CountedBounce.lean`: a DD-counted
reverse bounce, equivalence with the existing relation, and terminal/selected-path
adapters. Candidate returned; primary adopts it for checking. No build transfer.

Luna `circular_data` now owns only new `Circular/ParallelPathsGeneral.lean`
and `Circular/RawBounceContacts.lean`: generalized saturated-path separation
and raw main/parallel contacts without requiring the terminal row to be strict.
Candidates returned; primary adopts both and completes the geometric separation
adapter. No worker edit lane remains active and no build transfer occurred.

Next bounded lane: Luna `circular_data` owns only new
`Circular/UnstrictCorner.lean`, exposing a strict corner as normal without
changing area, inverse strictification, deletion compatibility, strict-row
behavior, and the actual R1 identities. Build-free; primary retains integration.

Aristotle direct-DN project `a768ca01-7392-49a9-b695-339de82ec027`, task
`847a2439-f8d6-4124-8cb3-222377ca36f9`, is COMPLETE. Final `Result.lean` is in
external `circular-dn-orientation/`; primary is porting the concrete geometry and
main identity. No source acyclicity or ordinary-cut assumption was added.
Primary owns new `DNLocalData`, `DNSwapGeometry`, `DNTargetData`,
`DNOrientationBlocks`, `SecondBounceOrientation`, and `SecondBounceRecurrences`
modules. Astra `circular_plan_review` audits DD propagation read-only.
Aristotle overlapping-ND project `eb5bc1c3-b026-45aa-9acb-6d3927797294` is active,
task `55de8e35-31e7-4ff2-a476-f26ac24fe345`, external `circular-nd-alias/`. Its request includes the locally checked
AliasMeasure and AliasRealization support. No local semantic identity yet.

Remaining: locally integrate direct-DN HRV; full DD propagation, alias-aware ND
identities, and final circular induction. Keep the active full goal open.
The alias natural-pair change removes old pairs `(f.tail,i)`, `(f.tail,f.head)`,
`(next f.tail,f.head)`; target normal pairs remove `(f.tail,i)`,
`(next f.tail,i)`, `(next f.tail,f.head)`. Do not conflate those identities.

Source-path drift: Overleaf `old-main.tex` is absent; `main.tex` now contains
the former long draft and `new-main.tex` is present. No Overleaf edits in this
continuation; earlier hashes and line references are historical.

