# Finite orientation and highest-reachable-vertex model

The reviewed finite-degree architecture applies without a symmetric-functions
library. Primary source audit and independent Terra review agree on the
following representation (manuscript lines 1267–1355).

An orientation chooses a Boolean direction for each normal edge. True means
ascending; strict edges are always ascending and are not counted in the
ascent statistic. The upward-step relation contains exactly strict edges and
normal edges chosen ascending. All these edges have increasing endpoints.
Reachability is its reflexive transitive closure, matching the source's
allowance to stay at the starting vertex.

The reachable vertices form a finite nonempty set for each vertex u. Define
hrv(u) by its maximum. The nonempty fibers of hrv are exactly the blocks of
the source partition. Define the elementary monomial by multiplying
`elementary (card fiber)` over the nonempty fibers, indexed by possible
representatives r : Fin n. Empty fibers contribute 1. This directly expresses
`e_lambda`: multiplication is commutative, so sorting block sizes is not part
of the mathematical definition needed by the theorem.

The unshifted expression is the finite sum over orientations of
`C ((Polynomial.X - 1)^asc) * hrvMonomial`. A separate shifted expression
uses `C (Polynomial.X^asc)`. The shift relation must be proved using the
coefficient substitution map. Equality with the coloring polynomial, the
recurrence clauses, positivity, and degree assertions remain proof obligations.

For n=0 there is exactly one orientation (an empty function), ascent count
zero, and empty monomial product 1. The HRV definition has a vertex argument,
so it never requires a maximum of an empty set.

Module boundaries:

- `Orientation.lean`: orientation choices, ascent count, upward steps and order.
- `HRV.lean`: reachability, maximum, and its characterization.
- `OrientationExpansion.lean`: fibers, elementary product, and finite sum.
- Later independent modules: column/concatenation identities, local recurrence
  bijections, shift/positivity, and degree. These are not assumed by definitions.

Mathlib APIs audited locally: `Relation.ReflTransGen`, its `refl`, `single`,
`trans`, and induction; `Finset.max'`, `max'_mem`, `le_max'`, `max'_le`.
Classical decidability is acceptable for finite reachability. A computable
transitive-closure implementation is not required for the initial theorem.

The column case is proved in `OrientationColumn.lean`: the unique orientation
has zero ascents, every vertex reaches the final vertex, and the only nonempty
HRV fiber has size k+1. `ColumnBridge.lean` combines this independent proof
with the previously checked coloring column theorem, uniformly in alphabet size.
