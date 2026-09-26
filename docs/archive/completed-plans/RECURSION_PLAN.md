> Historical plan. Completed results are in [COMPLETION](../../COMPLETION.md).
> The remaining restricted-recursion issue is in [the current audit](../../RESTRICTED_BOUNCE_AUDIT.md).

# Recursion and termination prerequisites

Claude Sonnet independently audited the source and current model, read-only.
Primary checked the report against manuscript lines 1853–2044. Its external
prompt/result are in the `recursion-audit` request directory recorded in the
handoff. This file records the accepted plan, with corrections to the draft
certificate. These are future proof obligations, not a completed recursion.

## Measure and exhaustive cases

Use the lexicographic measure `(n, eastCount, firstEastHeight)` on valid paths.
The height is the absolute vertical coordinate immediately before the first
east step. A total natural-valued implementation may assign zero to the empty
path; positive-size paths must be proved to have an east step. There is no
need to leave the measure undefined at the empty normalization case.

Write a nonempty path as `X ++ east :: W`, with X containing no east step and
ending at `(x,z)`. Its first step must be north, so X is nonempty. The source
uniqueness proof is at 1996–2044.

| Case | Reduction | Strict decrease and missing word facts |
| --- | --- | --- |
| Empty path | Value 1 | Separate normalization, already checked for coloring semantics. |
| Exactly one east | `north :: replicate (n-1) diagonal ++ [east]` | Base value e_n. Prove the converse classification; current column lemmas construct and evaluate the column only. |
| At least two east steps, z=x+1 | Split after the first east | Both sizes are strictly below n. The suffix must be translated from `(x+1,x+1)` to the origin. Prove its validity and both nonzero sizes. |
| z>x+1 and X ends north | Replace the final north/east by diagonal, or by east/north | The diagonal successor has one fewer east step. The east/north successor has the same east count and first-east height z−1. |
| z>x+1 and X ends diagonal | Apply generalized bounce reduction | All resulting paths have the same size and east count and smaller first-east height. Single-bounce relations alone do not justify this case. |

Before the converse column classification, prove endpoint step-count formulas
and equality of north/east counts for valid paths. These facts also support
the first-east decomposition and the product-size bounds. Do not infer the
converse classification merely from `coloringLLT_column`.

An eventual reduction certificate should record exact successor word
identities, valid paths, and strict measure decreases. A product constructor
needs two independent sizes n₁,n₂ with n₁+n₂=n, not two factors of one shared
size. Algebraic identities follow separately from `SatisfiesRecursion` and
the proved generalized bounce relations. A list of smaller paths alone does
not certify the intended recurrence. The precise Lean certificate should be
chosen once the generalized-bounce interface is available.

## Separate generalized-bounce induction

Theorem `bounce_reduction` (1853–1993) keeps the no-east restriction on V and
allows an arbitrary number of bounce points. Its induction measure is the
number of bounce points, separate from the triple above. The one-bounce base
uses the two recurrence clauses and the north/diagonal relation from
`equivalentRelations`. Deriving that third relation from the restricted
recurrence has a newly identified proof obligation; see
`RESTRICTED_BOUNCE_AUDIT.md`. Do not assume it as already derived.

For more bounce points, expose two consecutive diagonal steps at the next
return and apply the unicellular relation. The resulting terms use the
single-bounce clause and the induction hypothesis at `(v,y)` or `(v,x)`, each
with the top bounce point removed. A final unicellular relation recombines
the terms. All transformed words and smaller bounce decompositions need
validity and geometry proofs; they cannot be supplied by the outer measure
induction before this theorem exists.

The displayed proof has one common factor `1/(q−1)` from the first
unicellular decomposition, distributed across two terms. It does not require
two nested inverse factors. In the integral model, prove the equality after
multiplication by q−1, then cancel that nonzero factor. Do not copy the
consultant's informal “two prefactors from the IH” description literally.

## Integral cancellation

For every variable type σ, `MvPolynomial σ (Polynomial ℤ)` is a domain. This
covers both finite-variable coloring polynomials and formal elementary
expressions. Prove once that `C (Polynomial.X−1)` is nonzero and that left
multiplication by it is injective. No fraction field is needed for these
concrete rings. The warning in `FORMALIZATION.md` remains correct: a theorem
over an arbitrary ℤ[q]-algebra would need an explicit cancellation hypothesis.

The manuscript's base-value typo at 2010 remains e₁, not the integer 1. The
proof's W is a suffix word despite the missing star in its displayed alphabet
notation. Neither discrepancy changes the immutable reference files.

Completing the word/decrease layer and recursion uniqueness still does not
identify a recursively defined expression with `coloringLLT`. Preserve the
named coloring bridge and the separate orientation/HRV bridge required by
`FORMALIZATION.md`. Generalized bounce is an unfinished dependency to prove,
not an external blocker or a reason to add assumptions to the main theorem.

## Implemented word prerequisites

`ColumnCharacterization.lean` proves `Step.valid_one_east_column` and
`Step.valid_one_east_column_size`: every valid path with exactly one east
step has word `north :: replicate k diagonal ++ [east]` and size `k+1`.
This supplies the converse classification needed by the one-east case.

`FirstEast.lean` defines total `Step.firstEastHeightFrom` and
`Step.firstEastHeight` (zero when no east occurs). It proves the first-east
word decomposition, the count formula for its height, and
`Step.firstEastHeight_append_east`, identifying that height with the prefix
endpoint's second coordinate. These facts establish the intended measure's
meaning; strict decreases and the complete recursive reduction are still open.

`NorthEastReduction.lean` constructs the valid `ne → d` contraction and
`ne → en` swap under the strict prefix gap. It proves the east-count decrease
for contraction, unchanged east count for the swap, and first-east-height
decrease by one when U contains no east. These supply the arithmetic part of
the north-predecessor reduction; the full exhaustive certificate is still open.

`PathSplit.lean` constructs `prefixAtReturn` of size k and `suffixAtReturn`
of size n−k from a valid concatenated word whose prefix ends at `(k,k)`.
The suffix validity is translated back to the origin. `ProductReduction.lean` now proves strict positivity and strict size decreases
for the first-east split, and factorization for any `SatisfiesRecursion` witness.
`NonemptyPath.lean` proves that size zero is equivalent to the empty word,
and that every positive-size path contains an east step.

`RecursionMap.lean`, `SatisfiesRecursion.map`, transports every named recurrence
field through a ring homomorphism. In particular it will transport formal
orientation recurrences through `evalElementary`, once those recurrences have
been independently proved. It does not assume their existence.

`NorthPredecessor.lean`, `firstEast_north_reduction`, packages both valid
successors, the strict east-count decrease for contraction, the strict
first-east-height decrease for the swap, and the generic value identity.
`ProductReduction.lean`, `firstEast_product_reduction`, supplies positive
factors of strictly smaller size when the first-east prefix has gap one and
the source has at least two east steps. These are conditional branches;
exhaustive branch selection and the diagonal-predecessor branch remain open.

## Word-valued proof interface for generalized bounce

Use a small proof adapter `SchroderPath.evalWord F n w`: evaluate F on the
valid path with word w when its Boolean validity check is true, and use zero
otherwise. Every recurrence lemma for this adapter retains an explicit
validity hypothesis. The zero convention is not a new LLT definition or a
claim about invalid words. It lets the DD induction compare ordinary lists
without repeatedly transporting dependent path proofs. The final theorem
must return to F on valid paths via `evalWord_of_valid`.

The generalized theorem will quantify over every continuation W and size n,
a seed Y, an indexed `BounceDecomposition Y U V s t`, and validity of Y e W.
Induct strongly on length Y; the raised child A n d is not structurally a
subproof, so ordinary induction on the certificate alone is insufficient.
At a DD parent Y=A dd V₁ d, the two children A d and A n d have strictly
smaller length. Seed and decomposition closure for the raised child must be
proved, not supplied as extra assumptions.

Write A=U s t V₀. Unicellular resolution of the second DD step gives
A d n e V₁ d e W minus A d e n V₁ d e W. The first term uses the local DN
leading-east clause, followed by the raised-child induction hypothesis.
The second uses the ordinary-child induction hypothesis, then local DN.
For each terminal replacement B of A, these give B n e d V₁ e d W and
B e n d V₁ e d W. Their difference recombines to
(q−1) F_(B dd V₁ ed W). The NN, DN, ND terminal cases have coefficients
q; 1; and (q−1),q respectively, so the same linear calculation covers all
three. Cancellation is explicit. All local return/gap certificates and all
intermediate valid words must be derived from the existing geometry.

The word interface and linear DD step are now checked. In particular,
`SatisfiesReductionRecursion.generalizedFirstBounce_word` proves arbitrary
NN traces by strong induction on prefix length. Its exported
`generalizedFirstBounce` returns a genuine valid path, the value identity,
unchanged east count, and strict first-east-height decrease. The DN/ND
inductions and matching path packages are now checked as well; uniqueness
remains open. `GeneralizedBouncePath` already
provides valid successors for all three terminal pairs independently of the
value induction. Terra audited the two-child induction and local DN geometry.

## Exhaustive uniqueness implementation boundary

All three generalized bounce packages now return valid successors, equal east
counts, and strictly smaller first-east heights. `firstEast_prefix_cases`
proves that every east-free prefix ending at the first east step either has
gap one, ends north at a strict gap, or is a `BounceSeed`.

Implement `SatisfiesReductionRecursion.unique` for two witnesses with the same
q and column values in a domain and q−1 nonzero. Use nested strong induction
on size n, east count, then first-east height. At n=0 use empty normalization.
At east count one use `valid_one_east_column_size`. For larger east count,
extract the first east step and apply `firstEast_prefix_cases`. Gap one uses
product reduction and smaller sizes. The north branch uses unicellular
reduction: the contracted path has smaller east count; the swapped path has
smaller height. A bounce seed yields `trace.decompose`; `parts` excludes east
and DD terminal pairs, leaving NN, DN, ND. Apply the corresponding generalized
package for each witness and identify successors by their proved step words.

No new abstract recursive invariant is necessary for this uniqueness proof.
This proves uniqueness for the explicitly stronger sufficient certificate,
not for the unchanged manuscript-facing restricted predicate. It will give
the semantic bridge only after an independent orientation witness is proved.

The implementation above now checks locally: `ReductionUniqueness.unique`
(in namespace `SatisfiesReductionRecursion`) and the modular
`BounceAgreement.bounce_agreement`. The finite-variable characterization is
`coloringLLT_eq_of_satisfiesReductionRecursion`. The stronger-certificate
boundary remains unchanged.
