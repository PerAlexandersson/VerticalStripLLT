# Restricted recurrence and the third bounce

Status: a proof obligation identified during source audit, not a counterexample
to the manuscript or a claim that its theorem is false. Terra checked the
local relation diagram below; primary checked the cited source. A separate
Claude Sonnet audit completed and independently confirmed the local diagram.
Primary accepted that conclusion, with the corrections below. Its prompt/output
live in the external
`restricted-bounce-audit` request directory.

The recurrence at `main.tex:851–871` restricts the middle word V to north and
diagonal steps. Proposition `equivalentRelations` at 1413 onward is stated
without that restriction. Its displayed derivation at 1797–1804 invokes the
first bounce with middle word `east :: V`. The generalized-bounce base case
at 1886 says that the equivalence proof also works with restricted V; this
particular invocation needs a further argument before using it in Lean.

Write words with n,d,e for the three step types, keeping U,V,W fixed:

    P = U nd V de W       Q = U nd V ed W       R = U dn V ed W
    K = U dn V de W
    A = U nn eV de W      B = U nen V de W
    C = U nn eV ed W      D = U nen V ed W
    E = U enn V ed W      H = U enn V de W.

Subject to the required validity/return certificates, the unicellular
relations give

    A − B = (q−1)P,       C − D = (q−1)Q,
    D − E = (q−1)R,       B − H = (q−1)K.

The restricted bounce instances legitimately give K=Q and H=qE. The
additional relation A=qC would imply

    (q−1)P = (q−1)((q−1)Q + qR),

and cancellation yields the third bounce. However, A=qC is the first bounce
with middle eV. It is not an immediate field of `SatisfiesRecursion`. Within
this local diagram it is equivalent to the desired third relation after
cancellation. This does not rule out a derivation using other global
recurrence instances; such a derivation remains to be found and checked.

## Formalization boundary

`SatisfiesRecursion` faithfully retains the no-east condition. Do not silently
strengthen it or advertise generic uniqueness after adding the third relation
as an unproved hypothesis.

The concrete first/second coloring proofs already establish stronger graph
facts for arbitrary middle words. Consequently the third coloring relation
can be proved directly without resolving this generic implication. That is
now locally verified as `coloringLLT_thirdBounce`, using the independently
proved `coloringLLT_firstBounce_general`. A future stronger relation interface may be
useful, but any use in the ordinary expansion must discharge its assumptions
independently for both the coloring and orientation expressions. The final
ordinary expansion must remain unconditional for every valid path.

## Review of the independent audit

Sonnet independently recovered the same missing local instance. Its stronger
sentence that the relation is “not implied” by the full restricted recurrence
is not established by this analysis and is not adopted. The audit proves only
that the displayed local diagram is insufficient; it supplies no global
counterexample or proof of nonimplication.

The proposed escape through an extra bounce point is also not adopted. Write
`endpoint U=(a,i)` and the endpoint just before the final diagonal as `(i,j)`.
Replacing initial nd by nne preserves displacement. In A=`U nn eV de W`,
the westward return at height i+1 still meets the point after the first north
step, incident to the following north step; the inserted east lies at height
i+2. It does not create the suggested extra bounce at this start. Moreover,
the generalized-bounce statement itself retains the no-east-middle condition,
so that theorem would not automatically license the eV instance anyway.

The generic missing implication remains open. The direct coloring third-bounce
proof can use already derived unrestricted scanner facts without this issue.

## Bounded Aristotle candidate, 2026-09-25

The isolated generic implication search terminated `COMPLETE_WITH_ERRORS`;
the requested target remains unproved. Its separate candidate theorem
`firstBounce_eastMiddle_not_derivable_up_to_size_four` constructs a witness
for the size-at-most-four truncation with e identically 1. For
U=[north], V=[], W=[east], its source and swapped values differ by q−1
instead of satisfying the requested relation. The archive reports a kernel
proof via exhaustive bounded enumeration and polynomial-list arithmetic.

Terra audited the exact six bounded clauses, path/split completeness arguments,
and lack of placeholders in that new section. Primary has not locally built
the roughly 400-line candidate; it remains external audit material, not a
project theorem. The only remaining placeholder is the original target.
One archive docstring has W=[]; the actual theorem correctly uses W=[east].

If locally validated, the result excludes an argument using only recurrence
instances through size four for arbitrary supplied e. It does not establish
nonimplication from the full recurrence, and e≡1 is not the manuscript's
independent elementary-generator specialization. The report's larger-size
Python explorations are unverified and do not justify a global conclusion.

The concrete ordinary expansion is now proved through the stronger sufficient
certificate. Both models independently satisfy its unrestricted single-bounce
instances, and `SatisfiesReductionRecursion.unique` supplies uniqueness.
See [REDUCTION_CERTIFICATE.md](REDUCTION_CERTIFICATE.md) and
[COMPLETION.md](COMPLETION.md). This does not resolve generic uniqueness or the
third-bounce implication from the unchanged restricted `SatisfiesRecursion`.
The bounded candidate above remains external, not a locally checked theorem.
