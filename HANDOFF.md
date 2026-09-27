# VerticalStripLLT handoff

## Current result and verification boundary

Active goal: **formalize the full circular component proof**, with ordinary
component assembly proceeding in tandem at the user's explicit request.
The complete ordinary and aggregate circular formulas are Lean theorems.
The full ordinary and circular **component** formulas have audited mathematical
proofs but are **not yet complete Lean theorems**.

Latest pushed checkpoint: `7d87874`, complete component grouping and balanced
reduction, **2045 library jobs, 2647 axiom entries**, standard axioms only.
The next increment compiles in focused checks: actual compatible ordinary
diagrams, orientation recovery, coloring and HRV transports, forward flip
transport, and the complete conditional circular-to-ordinary reduction.
`Circular.component_identity_of_forward_components` now proves the full circular
component identity assuming the same identity for every ordinary forward diagram.
The only remaining semantic theorem is the ordinary component identity.
Full library passes **2060 jobs** and **2743 axiom entries**, standard axioms
only. Source guard, line-width checks and `git diff --check` pass.

No placeholders, custom axioms or unchecked native proofs are allowed. Expected
axioms are only `propext`, `Classical.choice`, and `Quot.sound`. Builds use pinned
Lean 4.34.0 / Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Logs live under `/lake-cache/ai-projects/requests/VerticalStripLLT/circular-continuation/`.
Current logs: `circular-ordinary-reduction-library-build.log` and
`circular-ordinary-reduction-axioms.log`; focused reduction:
`circular-from-ordinary-build-3.log` (1615 jobs).

## Ownership and build discipline

Academic-account restart continues in `/workspace/lean/VerticalStripLLT`, branch
`main`. Primary owns all returned source, imports, inventory, docs and the sole
serialized Lean build slot. Inspect active Lean/Lake processes before every
build, including other projects. Use `lake-workspace`; never plain Lake. No new
worktree, account, or supervisor worker has been started.

User explicitly allows Luna/Astra subagents and requested an independent shorter
argument search. All agents are build-free. Current assignments:

- `component_review` (Astra): edit-idle; returned `HRVInitialSupport.lean`, which
  primary owns but has not built. It is excluded from the current checkpoint.
- `word_swaps` (Luna): edit-idle; returned `Components/MountainScan.lean`, literal
  finite mountain-word scan and continuation linearity, not yet built.
- `word_covers` (Luna): owns only `Components/WordOrderEmbedding.lean`; the
  earlier returned block cancellation files compile.
- `simpler_component_route` (independent Astra): edit-idle after the final
  circular-reduction audit. It proposed the accepted shortcut below.

The runtime Lean MCP is rooted in RealRooted. Source search and serialized wrapper
builds are the recorded fallback; see `suggestions/project-tool-routing.md`.
Runtime registry and `codex mcp list` were inspected earlier this continuation.
Git SSH has no loaded key; routine pushes use existing gh credentials with a
command-local HTTPS rewrite, without changing remotes or stored configuration:

```sh
git -c url.https://github.com/.insteadOf=git@github.com: \
  -c credential.helper='!gh auth git-credential' push origin main
```

## Accepted shorter circular route

The independent reviewer confirmed that exact correspondence with one ordinary
component is unnecessary. Choose one residue-compatible balanced potential q for
the entire original component C, and sort its injective lifts by a permutation σ.
The compatible natural intervals form a genuine ordinary forward diagram E.
Its orientation map Φ into D is injective and recovers every state of C. Put
S={η | Φη∈C}. Ordinary flips map to original flips, so S is a union of entire
ordinary components. Summing the ordinary identity over S proves the identity
on C. No original-to-ordinary flip reflection is needed.

Verified modules under `Components/`:

- `CompatibleLiftOrder`, `IntervalDiagram`, `CompatibleDiagramEdges`: sorting,
  interval closure, actual diagram construction, and exact compatible edge image.
  Ordinary lengths are rank gaps; they are never equated with physical lengths.
- `CompatibleDiagramOrientations`: actual orientation maps, injectivity/recovery
  and exact selected-relation conjugacy; original D is undecorated.
- `BalancedHRVTransport`, `SelectedColoringTransport`,
  `CompatibleDiagramSemantics`: actual per-state and full original-component sums.
  Arbitrary integer intermediates are covered, with no common-cut assumption.
- `ForwardFlipNormalization`, `BalancedCoverTransport`, `CompatibleDiagramFlips`:
  all six integer-cover tests transport, and the original retained long edge
  supplies the physical window. No global integer order isomorphism is assumed.
- `FlipClosedSums`, `CircularFromOrdinaryComponents`: actual quotient grouping of
  flip-closed sets, then complete conditional reduction to the ordinary theorem.

An independent Astra audit found no semantic defect in the diagram, orientation
and valuation modules. Final closure/reduction audit also found no semantic defect.
The earlier concrete finite companion, coefficient constancy, whole-component
undecoration and common-potential propagation remain independent foundations;
see the archived handoff for their exact declaration map and verification.

## Remaining ordinary assembly

Already verified: actual component word functional and its four-term relation;
finite Cauchy identity paired with the actual component strict enumerator;
full signed mountain equation (4); actual ordered `MountainProduct` expansion;
local and iterated signed-tail cancellation; full-word carrier criteria; unique
sink/ancestor-block and ordered-block HRV identification.

The independent shorter-route review recommends a literal continuation scan,
not a global ordered-partition bijection:

1. Define a finite mountain-word scan mirroring `MountainProduct`. Prove its
   contextual scalar-evaluation bridge for every word prefix, using central
   elementary coefficients and existing tensor/word multiplication lemmas.
2. Distribute its continuation into actual per-state compatibility indicators.
   Per-state compatibility does **not** descend to the word quotient.
3. For fixed forward η, induct on S_k={v | η.hrv(v).val<k}. The scan on exact
   support S_k equals the product of elementary coefficients of actual HRV fibers
   whose roots are below k. At the next peak, signed-tail cancellation forces the
   first block to be the actual fiber of k; the remainder is exactly S_k.
4. At k=n, combine with `componentScalarEval_cauchyProduct` and identify the HRV
   elementary product. Instantiate `component_identity_of_forward_components`.

`HRVInitialSupport.lean` is a returned, unbuilt candidate for the support and
first-block lemmas. `MountainScan.lean` is also a returned, unbuilt candidate. Neither is root-imported
or in the current axiom inventory. Preserve ownership during integration.
Arbitrary outgoing-closed supports are too weak for the extraction invariant;
use actual HRV thresholds. Arbitrary edge markers do not refine the aggregate
identity (the independent review found a triangle obstruction).

## Checkpoint history and archive

Earlier pushed checkpoints: `33cdecc` (whole-component undecoration and normalized
balanced lifts, 2041 jobs/2627 axioms), `0eac2b2` (coefficient constancy,
2033/2590), `d4af8ce` (tight flip reconstruction, 2029/2578), `6bf5f42`
(actual finite companion, 2017/2529), `f668154` (mountain equation (4), 1992/2416).
Detailed APIs, decisions, rejected candidate shortcuts and assignment history:
[balanced-reduction archive](docs/archive/component-foundation-through-balanced-reduction-20260927.md).
Final independent Astra audit confirms the circular reduction, including the
physical window, all cover tests, injective state transport and counting each
orientation once. The ordinary hypothesis is exactly the missing theorem.
MountainScan and HRVInitialSupport have been returned; all source ownership is
primary except the next build-free bounded assignment: Luna word_covers owns
only `Components/WordOrderEmbedding.lean`, sorted increasing/decreasing block
words transported through a strictly order-preserving embedding. This supplies
the natural-subset/Fin-subset adapter for the contextual scan bridge.
