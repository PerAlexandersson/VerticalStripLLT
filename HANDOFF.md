# VerticalStripLLT handoff

## Scope and verified results

The ordinary and full aggregate circular HRV expansions and e-positivity are
formalized. The full ORDINARY flip-component formula now has a complete
independently audited mathematical proof, as does the balanced circular case
by compatible lifts. These new component proofs are not yet Lean-verified.
Primitive unbalanced circular components remain open. The
[component status](docs/FLIP_COMPONENT_STATUS.md) is the research entry point;
[ordinary component proof](docs/proofs/COMPONENT_ORDINARY_PROOF.md) is the new
mathematical completion; [circular completion](docs/CIRCULAR_COMPLETION.md)
remains authoritative for the Lean-verified aggregate theorem.

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

## Active implementation batch

Starting from clean pushed `2b9421e`, the user explicitly requested parallel
Lean formalization with Luna and Aristotle. Primary owns the new
`docs/COMPONENT_FORMALIZATION.md`, `docs/proofs/COMPONENT_PERIODIC_WORDS.md`,
HANDOFF, proof status/index, Aristotle ledger, library imports and verification
inventory. Luna owns only `VerticalStripLLT/Components/WordRelations.lean`;
no other agent may edit it until release. Aristotle receives an isolated
conjugation-lemma request and no local source ownership. Primary owns eventual
`VerticalStripLLT/Components/WordConjugation.lean` integration. All delegates
remain build-free locally; the sole build slot stays with primary.

Astra and Terra have completed read-only circular audits: the periodic HRV-map
coefficient formula extends, but negative winding requires cancellation after
fiber evaluation; the ordinary four-word relation has explicit circular
boundary corrections. These are new prose results, not a circular proof.

## Ownership and checkpoint

Primary owns strategy, research notes, integration, and the sole global Lean
build slot. Only primary may use `lake-workspace`, after checking that no
other build is active. No slot transfer occurred. No Lean, shared Rust,
reference or Overleaf source changed; no compilation was needed or run.

This continuation began clean at pushed `14e061d`. Primary owns the new
`docs/proofs/COMPONENT_ORDINARY_PROOF.md`, the rewritten component status and
its archived predecessor, and linked proof/index/README/AGENTS/circular-goal
boundary updates. Primary also owns status-only corrections in
`docs/proofs/FLIP_COMPONENT_INDUCTION.md` and
`docs/proofs/COMPONENT_CORNER_DIFFERENCES.md`, preserving their valid
minimum-area and signed-recurrence lemmas. Astra and Terra independently audited the full argument.
Luna audited the current Lean interfaces and possible finite word model.
All three tasks finished read-only/build-free; no delegate owns editable files.
No new Aristotle task was started.

## Complete ordinary component proof and exact next step

The proof applies to arbitrary ordinary natural graphs and arbitrary corner
decorations, with no saturation, connectivity, forest or isolation assumption.

1. The existing exact HRV coefficient theorem gives the labeled-poset
   refinement and signed mountain-block formula for j_π. Both component sums
   use the SAME count m_C(π) of compatible source states.
2. Actual flips prove the contextual four-word identity
   m_C(ρacbσ)+m_C(ρbcaσ)=m_C(ρcabσ)+m_C(ρbacσ), a<b<c.
   Consecutive word positions make the required covers automatic. This keeps
   the original COMPLETE component label and supplies isolation directly.
3. Work in the finite word algebra modulo these relations and ALL repeated-
   letter words. The functional m_C annihilates its ideal.
4. With A=sum of lower letters and D(t) their decreasing product (1+t u_i),
   direct conjugation gives Ad_D(u_n)=u_n+t[A,u_n]. A short induction proves
   [A,D]=0; no external commutation theorem is needed. Inverse conjugation
   identifies ad_A^k(u_n) with the ordered mountain commutators, without
   a factorial.
5. The finite coloring product factors as F_n=(1+W_n)F_(n−1), with
   W_n=Σ_k e_(k+1)(X) ad_A^k(u_n). Prefix factors retain their order.
   Its two free-word representatives have coefficients Z_π and j_π.
   Equality IN THE QUOTIENT, paired with m_C, proves K(C)=E(C).

This is a complete mathematical proof of the ordinary statement. The existing
compatible-lift theorem transfers ENTIRE balanced circular components and
both sums, so their formula follows as well. No pointwise equality Z_π=j_π,
closure-fiber connectivity or auxiliary DN isolation has been assumed.
The prior 14e061d status is archived; its open ordinary isolation problems
are alternative stronger claims, no longer blockers for this theorem.

Next: (a) prepare the finite Lean integration, with actual component/permutation
and coloring/word bridges; (b) resolve primitive unbalanced circular components.
The current word proof uses one finite linear vertex order and cannot simply
be applied to the periodic cover. The existing winding reduction still leaves
that primitive case open. The full thread goal therefore remains active.

Luna's API audit found component interfaces only in `Circular/Flip.lean`
(`flipComponent`, `componentHRV`) and `Circular/ComponentSemantics.lean`
(`componentStrictEnumerator`). A finite `(List V →₀ ℤ)` module with all
contextual relations and induced concatenation is a possible implementation;
`Submodule.mkQ`/`liftQ` supply the additive quotient API. Concatenation must
be proved compatible before using ring operations. Existing aggregate Lean
bridges do NOT establish the new component semantic identifications.

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

The full uniform proof was independently audited, without enumeration or
compilation. Whitespace, all 156 local links in the 15 task-owned Markdown
files, exact-file scope and both initialization-ancestor checks passed.
Astra also rechecked the minimum-area normalization and signed deletion
recurrence against the author's proposal: the ordinary residual regrouping
is still open for that alternative route, but no longer needed for the
ordinary word proof. Circular strict-corner reinsertion can fail admissibility. No new polynomial family or computation engine was
introduced. The previous turn made progress (`14e061d`); this turn completes
the ordinary mathematical component proof and its balanced circular corollary.
Primitive circular components and Lean integration remain unfinished.

A Rust capability audit read the library guide, refreshed Cargo metadata and
searched the exact algebra APIs; no computation was ultimately needed.
Paper-cache was registered but had no callable search tool in this session.
A web cross-check read Blasiak--Fomin, arXiv:1608.05042v2, Corollary 1.3;
its commutation theorem motivated a check, but the final proof is self-contained
and does not depend on it. No private source was uploaded through web tools.

The previous handoff, including winding and recurrence chronology and exact
old observer status, is [archived through DN transport](docs/archive/flip-component-handoff-through-dn-transport.md).
It is historical, not an active work list. Earlier checkpoint history remains
in Git and the linked documentation archive. The current goal is active and
has made progress; the primitive circular proof and new Lean integration are not done.
