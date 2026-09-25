# A sufficient recurrence certificate for the concrete expansion

Decision: primary source audit and Terra's independent strategy review,
2026-09-25. This refines the proof route without changing the representation
or the unconditional final expansion statement.

Keep `SatisfiesRecursion` exactly as the manuscript-facing restricted clauses.
Its generic uniqueness theorem remains open. The attempted derivation of the
third single-bounce relation uses an NN instance with middle eV, outside those
clauses. The audit and external bounded candidate are recorded separately in
`RESTRICTED_BOUNCE_AUDIT.md`; no global nonimplication has been established.

For proving the main corollary, introduce a separate
`SatisfiesReductionRecursion q e F` extending `SatisfiesRecursion q e F` by
two extra fields: the first- and second-bounce identities with middle eV,
where V has no east steps, with the same valid-word, return, and strict-gap
certificates. Each extra identity must be proved directly for each model.
It is not an assumption in the final LLT expansion theorem.

The full unrestricted first-bounce identities are available from the source:
`orientations:bounceI` at lines 2924–2934 imposes no restriction on V. The
second orientation bounce statement at 3462–3475 is likewise unrestricted.
The former restrictions are commented out in the immutable manuscript. The
coloring NN identity is already independently checked as
`coloringLLT_firstBounce_general`; its DN graph proof also does not use hV.
Prove the unrestricted orientation identities from the orientation bijections.
Specializing NN and DN at eV supplies the additional fields for both models.

Reduction sequence:

1. Derive restricted ND from the additional eV field, the existing restricted
   NN/DN clauses, four unicellular equations, and cancellation of q−1.
2. Prove the generalized-bounce reduction for east-free middle words by
   induction on the checked prefix trace, including transformed-path validity.
3. Combine this with the checked product and north-predecessor certificates
   for lexicographic uniqueness by `(size, eastCount, firstEastHeight)`.

Work over an integral domain with explicit q−1≠0, or equivalently expose only
the required cancellation law. `EExpansion` and every `XPoly m` provide it.
Do not assume an arbitrary ring homomorphism preserves nonzeroness. Transport
the recurrence certificate through `evalElementary m`, then invoke the
independently proved cancellation fact in the target ring.

The resulting theorem must still be exactly
`coloringLLT P m = evalElementary m (orientationExpansion P)` for every valid
path P and every alphabet size m, with no recurrence, uniqueness, or bounce
hypothesis. Both sides are defined directly by their finite combinatorics.
Shifted positivity and degree/stability remain separate requirements.

This route proves the main expansion without first resolving the source's
exact restricted-recursion uniqueness theorem. Keep that difference visible
in the source map, handoff, and final theorem inventory. It is not legitimate
to rename the stronger certificate to `SatisfiesRecursion` or claim the open
restricted implication has been proved.

Implemented: `SatisfiesReductionRecursion`,
`coloringLLT_satisfiesReductionRecursion`,
`SatisfiesReductionRecursion.thirdBounce`, and
`SatisfiesReductionRecursion.map`. The generic third-bounce theorem constructs
both valid successors and uses the seven local equations followed by explicit
nonzero-factor cancellation. The map theorem transports identities only;
it does not claim preservation of the domain/cancellation hypotheses.
Generalized bounce and lexicographic uniqueness remain open.

## DD-induction correction

A subsequent primary/Terra source audit identified the second leading-east
requirement at `LLTe_1`, lines 1927–1933: the local DN relation applied before
the induction hypothesis has middle eV''. The initially implemented NN-only
certificate suffices for the checked single ND consequence, but does not by
itself justify this DD step. Add the DN-leading-east field explicitly and
transport/prove it alongside NN. The original restricted predicate remains
unchanged. Both unrestricted coloring semantic statements follow from their
existing graph proofs; the direct orientation bounce statements must still
be proved. No generic leading-east implication has been inferred silently.
