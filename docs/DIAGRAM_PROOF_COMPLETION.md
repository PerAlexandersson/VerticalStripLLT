# Component expansions by diagrams: completion audit

The ordinary component expansion is now proved by the diagram argument,
independently of the earlier word-functional proof. The theorem was completed
at `f2f396f`, exported and audited at `1b6d13e`, and streamlined at `55cfaf5`.
At `77cabb9`, the finite companion also gives the full circular component
theorem using this ordinary diagram proof. This report concerns these
committed checkpoints.

## Current source checkpoint

Cleanup at `98ad880` moves the independent older proof into `WordProof/` and
removes unused diagram modules. Public theorem contracts and the actual
circular consequence closure are unchanged. Independent read-only review
confirmed that no removed module was in that closure.

- The full library build passes, **2367 jobs** (`full-build-4.log`).
- The remaining **815** dedicated axiom queries match `axioms-5.log` in exact
  namespace-normalized order; all use only standard Lean axioms or none.
- Immutable log: `axioms-98ad880.log`, SHA256
  `6eee3af0725d74a361367ced0b5ef502716d8cb08a0ff4a4dd0a13ac0a50745a`.
- The circular theorem's **360-file** project import closure contains no
  `WordProof`, old component-expansion, word/scan or mountain module.

The larger historical inventories below also included unused helper modules;
the lower current count reflects their removal, not a weaker theorem audit.

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

## Circular component theorem

[CircularConsequences.lean](../VerticalStripLLT/Components/DiagramProof/CircularConsequences.lean)
adds `component_strict_eq_elementary_by_diagrams` for **every** circular
`Diagram n`, orientation and finite alphabet, with no forwardness assumption.
The weighted orientation-sum, evaluated elementary expression and positivity
forms have the same names with the `_by_diagrams` suffix. No balance,
connectivity, recurrence or assumed semantic identity is a final hypothesis.

The finite companion reduction `component_identity_of_forward_components`
receives the ordinary diagram theorem as its input. For each balanced circular
class, compatible lift sorting produces a forward diagram. The preimage of
the chosen circular component is a finite union of complete ordinary flip
components, possibly several. Applying the ordinary theorem to each component
and summing proves the balanced identity. The finite companion combines these
identities with the same integer coefficients for both valuations.

`BalancedHRVTransport` now imports `ForwardHRVBasic` instead of the unnecessarily
strong `ForwardHRV`. The circular theorem's 360-file project import closure
contains no old ordinary word/scan theorem. An independent semantic review
checked the public scope, the union-of-components argument, this import change
and the merge of the duplicate natural-edge relation into `DiagramProof.Basic`.

Verification at the circular-extension checkpoint `77cabb9`:

- The full library build passed, 2365 jobs (`full-build-3.log`).
- The dedicated inventory and `axioms-4.log` match all **860** queries in exact
  namespace-normalized order. Eleven declarations use no axioms; the other
  849 use only `propext`, `Classical.choice`, `Quot.sound`.
- An immutable copy is `axioms-77cabb9.log`, SHA256
  `157ccffa799595d35c9748be954636fc713ab52741fcd21f3997c538ba46ae6c`.
  The working name `axioms-4.log` was reused after the earlier 856-query audit.
- The broad audit in `verification-2.log` reports 2814 quoted results, including
  2809 axiom reports, without errors. The manifest-path warning is unchanged.
- The owner reports source guards passed for all 238 diagram modules and
  `BalancedHRVTransport`.

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
- At the earlier ordinary checkpoint, `axioms-3.log` and the then-current
  `axioms-4.log` contained all 856 dedicated
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
