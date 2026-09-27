# VerticalStripLLT handoff

## Scope and verified results

The ordinary and full aggregate circular HRV expansions and e-positivity are
formalized. The stronger formula for **each entire flip component**, ordinary
and circular, remains open. [Component proof status](docs/FLIP_COMPONENT_STATUS.md)
is the research entry point; [circular completion](docs/CIRCULAR_COMPLETION.md)
is authoritative for the completed aggregate theorem.

Verified Lean checkpoint: `18fbb4d`. Public declarations in
`VerticalStripLLT/Circular/Expansion.lean`, namespace `VerticalStripLLT.Circular`:

- `coloringLLT_shifted_eq_eval_shiftedOrientationExpansion`;
- `coloringLLT_shifted_eq_orientation_sum`;
- `coloringLLT_shifted_e_positive`.

These cover every valid circular diagram and finite alphabet, including the
empty alphabet, without recurrence, acyclicity or no-wrap hypotheses. The
full build passed (1908 jobs); `Verification.lean` checked 2037 inventory
entries using only `propext`, `Classical.choice`, and `Quot.sound`. External
logs are `circular-expansion-{build,full-build,axioms}.log`. Subsequent component
research is audited prose, not new Lean declarations. Initialization commits
`830cc6b`, `130f7e8` and the immutable reference files are preserved.

## Ownership and checkpoint

Primary owns strategy, research notes, external diagnostics, integration,
and the sole global Lean build slot. Only primary may use `lake-workspace`,
after checking that no other build is active. No slot transfer occurred.
No Lean, shared Rust, reference or Overleaf source changed in this increment.
No compilation was needed or run.

Preceding pushed checkpoints: `ce0628a` (exact HRV coefficients) and `e8d5a3d`
(remote scope correction). That goal turn made progress; this continuation
began clean. Primary owns `docs/proofs/COMPONENT_CHAIN_NORMALIZATION.md` and
linked proof/status/index/ledger updates. Astra and Terra supplied independent
read-only audits. Their tasks are finished; no delegate owns editable files.
No Lean declaration or build-slot transfer was made.

## Current mathematical result and exact next step

The author's minimum-area induction remains the main route. The saturated
envelope is the minimum-area realization. Ordinary strict-corner deletion
partitions whole source components into ENTIRE smaller target components.
Alternating deletion and mixed-cycle cancellation localize a minimal component
defect on states acyclic after reversing strict corners. The exact HRV-map
coefficients are 0,+1,−1, with the proved outgoing-support count. These remain
in [corner differences](docs/proofs/COMPONENT_CORNER_DIFFERENCES.md) and
[exact HRV differences](docs/proofs/COMPONENT_HRV_DIFFERENCES.md).

New [strict-chain normalization](docs/proofs/COMPONENT_CHAIN_NORMALIZATION.md):

- Strict edges partition ALL vertices into increasing chains, including
  singleton blocks. Process these by decreasing maximum vertex.
- For a terminal chain with no outgoing normal at its last vertex, a
  reachability-minimal normal exit supports an actual strict-long flip into
  that chain. It preserves mixed acyclicity and decreases the number of exits.
- The union of processed chains is absorbing in both the ordinary and mixed
  graphs. Restrict to remaining vertices, normalize the next chain, and lift
  its flips back: a cover-testing path cannot enter that union and return.
- The resulting map P keeps a normal u→v if its strict-chain maxima increase;
  otherwise it replaces it by v→succ_S(u). It is explicit and idempotent;
  replacements within a state never collide. It preserves normal cardinality
  and the original component. A normalization path has exactly as many flips
  as the initial number of decreasing-chain-maxima normals.
- All anchors respect ONE fixed mixed-graph order: strict chains increasing
  by maximum, vertices decreasing within each chain. P is NOT a component
  invariant, and different anchors can lie in the same complete component.
- A P-fiber is the mixed-acyclic subset of a cube of rotatable anchor-edge
  choices. It is connected by actual flips. Its coloring difference is
  (−1)^|S| times an explicit enumerator with outside-closed-interval constraints.
  A single fiber need not have equal K and E sums.
- A strict-long flip between mixed-acyclic states either stays in one fiber,
  or induces ab↔cd across crossing strict corners ac,bd. This classifies
  its normalized endpoints; a direct two-flip path with normalized exterior
  is NOT assumed valid without its cover tests.

An attempted stronger normalization eliminating every normal from every
strict tail is false; the owned note retains the exact S={13,24}, N={12,34}
counterexample. The proved ordered normalization allows edges into earlier
processed blocks. Singleton blocks and the absorbing UNION are essential.

Next: build a recurrence for these anchor contributions and reconstruct
whole components, using strict-corner slides and the images of normal-long
flips. Paths through mixed-cyclic states must also be controlled. Fixed-color
connectivity, vertex-color-preserving HRV matching, and fiberwise K=E are all
false. The DN completion graph, exact signed HRV counts and smaller-component
corrections remain available; no single-active-component assertion is required.
The complete ordinary and primitive circular component formulas are still open.
The aggregate circular theorem is fully formalized.

## Consultation outcome and verification provenance

Aristotle project `3fd0ed1d-ba60-404b-8b99-beaaae1c4d08`, task
`4aa8cbee-7eb5-4d15-ba07-7806c7fa540a`, is terminal **COMPLETE**. The full
return explicitly does NOT prove the residual identity or a uniform recurrence.
Primary downloaded and read `RESIDUAL_BRIDGE.md`; exact archive/input/proof
hashes belong in [the ledger](docs/ARISTOTLE.md).

Primary accepted the residual diamond calculus and checked its explicit
obstruction: weighted corner-long pairs in the already-proved K4 tree
component force target multiplicities t,0,1−t along two actual flips.
Thus corner-long pairs alone cannot reconstruct whole smaller components.
The owned HRV note records the proof. Shorts stay NORMAL in the valid
corner-deletion target; they cannot be arbitrarily declared strict.
No generated Lean or experiment source was integrated.

Both observers `83731`, `72078` ended after stream interruptions. Direct SDK
reads revalidated the same remote task and later confirmed its terminal state;
no replacement task was started. The remote reports its n=7 scan timed out
and no enumeration remains. Scans were outside the requested scope from the
start; their claims about small cases are not used as proof. No live remote
task, observer or delegate remains, and no new consultation is queued.

External requests root: `/lake-cache/ai-projects/requests/VerticalStripLLT/`.
This return is in `mixed-corner-residual/`. Earlier bounded local predicate
receipts and Rust capability audits remain documented in the linked notes.
No new computation engine, polynomial family, shared Rust edit or build was
introduced in this increment. The Overleaf recurrence sketches were reread
without edits; their global component regrouping obligations remain open.
AXLE is registered; Lean MCP targets RealRooted; Aristotle uses its installed
CLI/SDK. No credentials were printed or committed.

## Checks and history

Checks passed: `git diff --check`, focused diff review, all 106 local links
including heading anchors across seven Markdown files, and both initialization
commits remain ancestors. Lean/reference/Overleaf sources are unchanged; no
build was needed. This handoff accompanies the strict-chain normalization
checkpoint on `main`; its exact hash is in Git history. The continuation made
progress through an independently audited theorem, exact fiber semantics and
an audited obstruction; it is not a completion claim.

The previous handoff, including winding and recurrence chronology and exact
old observer status, is [archived through DN transport](docs/archive/flip-component-handoff-through-dn-transport.md).
It is historical, not an active work list. Earlier checkpoint history remains
in Git and the linked documentation archive. The current goal is active and
has made progress; neither the full proof nor its Lean formalization is done.
