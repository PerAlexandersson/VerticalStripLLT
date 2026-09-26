# Circular bounce selection and local recurrence interfaces

We work directly with the periodic boundary b(z) = z - a(z mod n).
This avoids choosing an ordinary cut. The checked boundary is monotone and
satisfies b(z+n*k) = b(z)+n*k. Let s(z) indicate a strict row and set

    g(z) = b(z+1) - b(z) - s(z).

The integer g(z) is nonnegative. The boundary contributes a diagonal step at
strict rows and a north step at other rows, followed by g(z) east steps.
This row interpretation motivates the definitions; the proof uses the actual
area function and strict-edge relation throughout.

## Finding the seed

Assume every corner is strict, the strict relation is acyclic, and a normal
edge exists. Some area is at least two: if all areas were at most one, every
edge would be a corner and hence strict. Choose a row of maximal area M.
There is a row z leaving this maximal plateau. Otherwise all cyclic successors
would remain maximal, making the entire area sequence constant and positive.
Every vertex would then have an incoming strict edge, contradicting acyclicity.

At a plateau exit, a(z) >= 2 and a(z+1) < a(z). This row is strict and g(z)>0.
It is an eligible terminal DE marker. This is the theorem
`Diagram.exists_eligible_seed` in `Circular/BounceSeedExistence.lean`.

## Reverse search with restarts

Maintain a strict current row t with a(t)>=2 and put x=b(t). We have x+2<=t,
so monotonicity gives b(x+1)<=x.

If g(x)>0, then a(x)>0: otherwise b(x)=x contradicts the positive boundary
jump. Corner saturation makes x strict. Also a(x)>=2, since a(x)=1 would give
b(x+1)=x+g(x)>x. Thus x is itself an eligible DE marker. Restart there,
discarding the previous contacts.

If g(x)=0 and both x and x+1 are strict, this is a DD contact. Here
b(x+1)=b(x)+1 and b(x+2)>=b(x)+2. Since b(x+2)<=b(t)=x, we again have a(x)>=2.
Continue at x and retain the contact. Otherwise we have a terminal NN, DN,
or ND contact.

Every continuation and restart follows the actual source strict edge x->t
backward. The number of strict ancestors of the current residue therefore
strictly decreases. The search terminates; its contacts since the last restart
form a complete reverse bounce from an eligible seed.

`Diagram.exists_complete_reverseBounce` in `Circular/BounceSearch.lean`
proves this for every diagram satisfying the three hypotheses. Its result
contains `EligibleDE z` and `ReverseBounce D z x`; `terminal_types` proves
NN/DN/ND exhaust the outcome, and `selected_path` identifies the path in the
unchanged source strict graph. No semantic recurrence or successor validity
is assumed in this search theorem.

## Local semantic interfaces

`PairGraph` is an endpoint presentation of finite directed edges. The theorem
`Diagram.pairGraph_coloringLLT` proves equality with the original edge-instance
coloring definition; circular edges are uniquely determined by their ordered
endpoints because their natural lengths are positive and less than n.
`PairBounce` ports the existing NN/DN coloring involutions without requiring
an ordinary path. All exterior swap hypotheses remain explicit.

`ShortenStrict` constructs the terminal DE->ED diagram by deleting the strict
corner and marking its shortened edge. Its corner proofs are derived from
the strict area drop at the next row. `ShortenStrictPairs` proves the exact
strict and normal endpoint changes. `FirstBounceColoring` instantiates the
NN involution on this actual target. `FirstBounceGeometry` discharges the
exterior hypotheses from the NN row flags and terminal gap, proving
`Diagram.coloringLLT_firstBounce_geometry` for every finite alphabet.
`ReverseBounce.exists_contacts` extracts the strict main and parallel integer
chains; the full DN successor and finite-index contact adapter remain to be
connected to the previously checked neutral-rank theorem.

For orientations, `Orientation.liftedHRV_conjugate` transports the actual
integer-cover maximum through a lift isomorphism whose order is preserved on
sinks. `PeriodicSwap` proves that an adjacent periodic transposition preserves
order on any set not containing both vertices of a swapped pair. A selected
outgoing edge at the first vertex excludes that pair of sinks. Consequently
`Orientation.hrvMonomial_periodicSwap` preserves the actual circular HRV fiber
monomial under the explicit lifted-step correspondence.

`PeriodicBoundarySwap` proves natural lifted-edge invariance outside the
periodic adjacent bridges from equal adjacent boundary values and the missing
boundary value at the terminal DE gap. These are whole-period statements;
there is no nonwrapping window assumption.

## What remains for the full expansion

The complete contact search is proved. It does not yet prove all successor
updates or the required polynomial identities. The remaining work is to:

1. instantiate the coloring and HRV recurrence adapters for every terminal
   contact type, including the periodic exterior;
2. propagate the local identities through the intervening DD contacts;
3. derive `FullNeutralBounce` for the actual DN successor, so the previously
   proved strict-rank decrease applies;
4. close induction with doubled geometric half-square area first, and strict
   rank for the neutral branches, using the checked strict-cycle and no-normal
   base families.

The main circular coloring–HRV equality is still an explicit theorem target,
not an assumption imported by this work.

## DN successor geometry (next implementation)

For a terminal DN row x and outer eligible DE row z, raise area at x+1 by
one and lower area at z by one. Remove the strict flag at x, add it at x+1,
and retain z. Writing a=b(x) and p=b(z), the exact strict replacement is

    {a -> x, p -> z}  becomes  {a -> x+1, p+1 -> z}.

All DD contact edges remain unchanged. The normal edges remove p+1 -> z and
add a -> x. The builder requires distinct residues of x and z, and of x+1
and z, together with a(x)+1<n. Acyclicity of the full main path and its
separation from the closed parallel path imply these conditions, including
exclusion of a length-n new edge. The local validity proof then uses only
boundary monotonicity and the terminal gap. Both area sum and strict-edge
count are preserved. These are mathematical derivations pending their Lean
successor constructor, not hypotheses to add to the final expansion theorem.
