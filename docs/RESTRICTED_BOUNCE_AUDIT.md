# Restricted recurrence and the third bounce

Status: a proof obligation identified during source audit, not a counterexample
to the manuscript or a claim that its theorem is false. Terra checked the
local relation diagram below; primary checked the cited source. A separate
Claude Sonnet audit is examining possible alternative decompositions or
noncircular derivations. Its prompt/output live in the external
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
the current Aristotle target. A future stronger relation interface may be
useful, but any use in the ordinary expansion must discharge its assumptions
independently for both the coloring and orientation expressions. The final
ordinary expansion must remain unconditional for every valid path.
