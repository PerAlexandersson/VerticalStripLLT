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
