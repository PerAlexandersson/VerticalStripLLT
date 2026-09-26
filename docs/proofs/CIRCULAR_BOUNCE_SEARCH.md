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
chains. `IndexedBounceContacts` converts them to finite indexed paths;
`DNContactGeometry` proves their separation and the needed circular length bounds.
`DNRealization` constructs the actual valid DN successor and its full neutral
contact witness, and `GeometricArea` proves area preservation and rank decrease.

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

## Independent NN orientation recurrence (now checked)

`Diagram.shiftedOrientationExpansion_shortenStrict_NN` in
`Circular/FirstBounceOrientation.lean` proves the `(X+1)` recurrence for the
original HRV expansion. Its proof expands over subsets of normal edges, with
cyclic subsets contributing zero. Relative to a base subset, there are four
choices for the bridge and shortened edge. Actual lifted-HRV potential
comparison proves their additive local identity. The bottom pair is matched
by the full periodic swap; the top pair has identical reachability after
substituting the two-step bridge/shortened-edge path for the old strict edge.
The swap of base subsets preserves cardinality, giving the coefficient identity.

`FirstBounceRecurrences` aligns both independent recurrences in the same
coordinates and proves the semantic induction step, assuming equality only
for its smaller target. `ShortenStrictMeasure` proves that target doubled area
is exactly two less. These are uniform theorems for every circular size and
finite alphabet, without a cut or no-wrap hypothesis. They currently concern
a single NN contact; DD propagation is a separate remaining step.

## Current proof boundary

Direct NN and DN identities are proved independently for coloring and actual
HRV semantics. The complete reverse search and full DN target measures are
also proved. The outstanding generalized DD/ND identities and final induction
are maintained in [the active goals](../CIRCULAR_GOALS.md), with the checked
interfaces indexed in [circular status](../CIRCULAR_STATUS.md).

## DN successor geometry (now checked)

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
count are preserved. `Diagram.exists_area_preserving_dn` proves these facts for every complete
acyclic DN search. `doubledArea_int` identifies the natural-valued measure with
twice the intended geometric area. These are consequences of the source
geometry, not extra assumptions of a circular expansion theorem.
