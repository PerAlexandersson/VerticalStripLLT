# Ordinary component expansion by diagrams: completion audit

The ordinary component expansion is now proved by the diagram argument,
independently of the earlier word-functional proof. The theorem was completed
at `f2f396f`, exported and audited at `1b6d13e`, and streamlined at `55cfaf5`.
This report concerns those committed checkpoints, not subsequent dirty Lean
work in the shared checkout.

## Scope

The public declarations in
[Consequences.lean](../VerticalStripLLT/Components/DiagramProof/Consequences.lean)
are in `VerticalStripLLT.Circular`:

- `component_strict_eq_elementary_of_forward_by_diagrams`;
- `component_weighted_strict_eq_eval_of_forward_by_diagrams`;
- `component_weighted_e_positive_of_forward_by_diagrams`.

For every forward diagram, every actual orientation and every finite alphabet,
the first theorem identifies `componentStrictEnumerator D θ m` with
`evalElementary m (componentHRV D θ)`. Arbitrary permitted original strict
markings are retained. The other two theorems restore the common selected-edge
weight and give homogeneous elementary positivity. No recurrence certificate,
common-cover witness or assumed equality is a hypothesis of these statements.
The project represents positive-size diagrams; the empty-diagram identity is
the usual empty product.

## The diagram proof

The proof uses actual flips, preparation and crossing slides with the exterior
restored. Complete-diagram and inherited-clique paths give common-cover
uniqueness. Alternating corner deletion, absent-corner deletion and weak-block
reordering give the three smaller corrections. NN/DN identities on complete
edge layers then isolate the whole component containing a witness.

The first-drop argument unmarks an incoming strict corner when necessary,
using a correspondence of whole components. Prefix selection supplies the
initial path and nontrivial block needed for this argument. Endpoint-marked
coloring and HRV identities attach the resulting signed list of components to
the fixed right component, with the same coefficients on both sides.

`component_eq_by_diagrams_aux` closes strong induction on vertex count,
natural area and the sum of natural-edge heads. Disjoint natural blocks
factor, saturation preserves the measure, and every attached recurrence
target is strictly smaller. The path base uses its actual selected-coloring
and HRV semantics. See the
[draft correspondence](drafts/README.md) and
[Lean coordination report](LEAN_COORDINATION.md) for the individual maps.

## Verification

Only the designated Claude owner ran Lean. Codex independently reviewed the
source, proof contracts, dependency closure and resulting logs.

- The full `VerticalStripLLT` build passed at `1b6d13e`: 2364 jobs in
  `full-build-2.log`.
- The post-refactor focused build passed through `Consequences`: 1921 jobs in
  `clean-4.log`.
- Both `axioms-3.log` and the refreshed `axioms-4.log` contain all 856 dedicated
  queries in exact order, allowing Lean's namespace qualification of printed
  names. All declarations use only `propext`, `Classical.choice`, `Quot.sound`,
  or no axioms. In particular there is no `sorryAx` or `Lean.ofReduceBool`.
- At `1b6d13e`, the final theorem's local import closure contains 289 files.
  The dedicated verification closure contains 314 including its entry point
  (313 imported files). Neither uses the earlier word/scan component proof.
  Semantic positivity helpers do not import that proof.
- All 237 diagram modules passed source guards and the 100-column check.
  Independent review approved the full induction and the semantics-preserving
  refactor at `55cfaf5`.

Logs are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/claude-right-attachment/logs/`.
The full build also restored a missing direct `Circular.ComponentSemantics`
import in `CompatibleDiagramSemantics`; its declarations did not change.

The circular aggregate expansion has its separate
[completion audit](CIRCULAR_COMPLETION.md). Its proof is independent of the
ordinary component theorem. The combined manuscript is a separate writing
deliverable; formal verification does not by itself certify its exposition.
