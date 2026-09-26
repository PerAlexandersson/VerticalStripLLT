# Circular implementation goals

The architecture is recorded in `CIRCULAR_FORMALIZATION_PLAN.md`. This ledger
fixes the first proof targets before integration. Names are proposed until the
corresponding module is checked. All polynomial equalities quantify over every
finite alphabet, including zero. Circular size is positive.

## General targets now take priority

The user requested full statements and isolation of examples. The original
first checkpoint below is complete; example modules are under `Examples/`.
The general selected-orientation identity and acyclic walk bounds are locally
proved. Actual lifted HRV, its greatest-reachability characterization,
translation/lift independence, and the degree and coefficient positivity of
the independent HRV expansion are also locally proved. The remaining main
target is the full circular semantic bridge:

```lean
theorem coloringLLT_shifted_eq_eval_shiftedOrientationExpansion
    {n : ℕ} (D : Diagram n) (m : ℕ) :
    xQShift m (D.coloringLLT m) =
      evalElementary m (shiftedOrientationExpansion D)
```

This exact statement, with no recurrence or expansion assumptions, is the
active Aristotle request `5835802e-8139-48b7-a07b-06add00f1f14`. It is not
yet an exported Lean theorem. See `CIRCULAR_REDUCTION_OBLIGATIONS.md` for the
parallel mathematical decomposition.

## General induction-base progress

`ZeroArea` proves that no non-strict arcs forces all natural arcs to have
unit length and makes both endpoint maps injective. `StrictCycleExpansion`
proves the full semantic equality whenever every vertex has an incoming
strict arc: both independent expressions vanish. `HRVRoots` proves that
actual HRV values are selected sinks, sinks are fixed, and HRV is idempotent.

The full zero-area family is now proved by
`coloringLLT_shifted_eq_expansion_of_no_normal`, for every D with
`D.edgeData.normalEdges = ∅` and every alphabet. The proof uses actual HRV
fibers, whose reachability orders are finite chains. `RootedChainCertificate`
constructs their increasing enumerations from acyclicity, root preservation,
and fiber comparability; `ChainColorings` proves the arbitrary disjoint-chain
product formula. The final theorem assumes no chain certificate or semantic
identity. The empty-orientation branch vanishes on both sides.

Separately, `CutOrder` proves cyclic area growth and the bound at a zero head;
`ZeroAreaIncoming` provides such a head when incoming strict coverage fails.
These are available for later cut transport, but the completed zero-area
proof does not need a conversion to ordinary paths. This does not justify a
cut for general circular diagrams.

## Completed first checkpoint

1. `Diagram` encodes cyclic area bounds and corner-restricted strict edges.
   Edge instances retain their natural direction, including opposite arcs.
2. `EdgeData.coloringLLT` is a direct coloring sum on a finite edge-instance
   graph. `Diagram.edgeData` specializes it to circular diagrams.
3. `EdgeData.strictOrderEnumerator_eq_zero_of_not_admissible`: a cycle in the
   selected strict/ascending relation makes the strict coloring sum zero.
4. For the two-vertex diagram with both natural arcs, prove the three cases:
   no strict arcs gives `e₁² + 2q e₂` after the q→q+1 substitution;
   one strict arc gives `e₂`; two strict arcs give zero.
   These must be equalities with the independent coloring definition, not just
   declared elementary expressions or bounded-alphabet calculations.

## Unconditional orientation checkpoint

Let N be the non-strict edge instances and A range over subsets of N. Write
K_strict(A) for the coloring sum imposing every edge in S union A strictly.
The exact semantic target is

    xQShift m (G.coloringLLT m)
      = Σ A ∈ N.powerset.filter G.Admissible,
          C (Polynomial.X ^ A.card) * G.strictOrderEnumerator A m.

First prove the sum over all subsets, then eliminate cyclic subsets with the
cycle-zero theorem. This theorem applies to arbitrary finite edge-instance
graphs; circular area geometry is not needed. A selects the ascending
non-strict edges, so its cardinality is the orientation ascent count.

Aristotle request `40998e1f-04ed-473c-9d58-5656253cfa9d` isolates the finite
algebra behind this identity. For a finite index type I, edge set t, predicates
ok and asc, weight w into a commutative semiring, and z, prove

    Σ i, [ok i] (z+1)^#{e∈t : asc i e} w i
      = Σ A⊆t, z^#A Σ i, [ok i and ∀e∈A, asc i e] w i.

Brackets mean an indicator implemented by an if-expression. The request has
no graph hypotheses, no HRV statement, and no circular source text.

## Subsequent circular HRV targets

Define lifted reachability using positive natural edge displacements, prove
the acyclic span bound (n−1)², and take the greatest reachable lift before
projecting. Establish translation invariance and agreement with ordinary HRV
when there is an ordinary cut. The final desired equality replaces each total
strict-order sum by the HRV elementary expansion; it does not assert that an
individual orientation's strict-order enumerator equals its HRV monomial.

The aggregate circular proof then needs geometric local reductions, a
same-state retained-coloring invariant for returning bounce markers, and a
proved secondary termination measure at fixed non-strict area. Keep these
explicit targets separate from the unconditional orientation checkpoint.
No recurrence certificate is to be assumed in the final coloring theorem.

## Delegation and proof boundaries

Primary owns strategy, integration, and all serialized local builds. Luna and
Terra return bounded build-free implementation or API audits; current exact
ownership is in `HANDOFF.md`. Aristotle's active request is the full circular
semantic bridge. Component work uses complete global components and full
lifted covers; weak/h and strict/e differ by the planned omega translation.
No component claim is assumed by the circular aggregate theorem.
