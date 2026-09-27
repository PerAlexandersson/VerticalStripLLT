# Circular flip interfaces

Source: the initial `LLT flip/old-main.tex` snapshot, lines 1939–1986,
as hashed in the archived circular plan. The current full proof is the
Overleaf `Circular Vertical-Strip LLT Polynomials-v9.tex`; see the
[comparison audit](proofs/COMPONENT_CIRCULAR_FACE_PROOF.md).
These foundations and the full aggregate circular expansion are locally verified.
Ordinary and all circular component expansions now have audited mathematical
proofs, pending Lean integration; the zero-normal component family is already
Lean-verified. See [the component proof map](FLIP_COMPONENT_STATUS.md).

## Full lifted covers

`Diagram.naturalLift e x y` means `residue x = e.tail` and
`y = x + e.length`. `Diagram.liftCover A x y` means x < y, full
reflexive-transitive reachability from x to y using `liftStep A`, and no
integer z strictly between them reachable from x and reaching y.
The relation is computed in the entire integer cover, not inside a selected
window or from projected covers. Positive lift increments prove that every
cover is a direct selected step. A natural lift identifies its edge instance
uniquely. Covers of normal edges therefore imply orientation membership.

## Exact directed flip witnesses

A `DirectedFlipWitness D θ η` has integers a < b < c < a+n and two normal
edge instances naturally lifted as a→b and b→c. All other edge instances
agree between θ and η. The source has covers a⋖b and a⋖c, but not b⋖c;
the target has covers a⋖c and b⋖c, but not a⋖b. Both are admissible
orientations by their types. `DirectedFlip` is existence of this witness;
`Flip` includes either direction.

The two toggle memberships and distinctness of the edge instances are proved
consequences, not additional hypotheses:
the covers force a→b selected at the source and b→c selected at the target.
Selecting b→c at the source would make b intermediate in its a⋖c cover;
selecting a→b at the target similarly contradicts its a⋖c cover. Thus exactly
one ascending normal edge is replaced by the other. This proves ascent
invariance without strengthening the manuscript definition.

## Complete components and target

`flipComponent D θ` filters the entire finite orientation type by
reflexive-transitive `Flip` reachability. It is the complete global component,
including every exterior or mixed flip. Ascent is constant throughout it.
The independently defined elementary expression is the sum of HRV monomials
over this component. The full strict/e target is, for every D, θ, and m,

    Σ η ∈ flipComponent D θ, strictOrderEnumerator η.val m
      = evalElementary m (componentHRV D θ).

This remains a theorem target, not a Lean assertion or a certificate assumed
by the implementation. The source weak/h statement is its omega-translated
form. That translation is to be formalized before finite-alphabet evaluation;
we do not identify weak and strict order enumerators by definition.

## Ownership boundary

Primary fixes these interfaces and owns integration and every local build.
Luna returned `Circular/LiftCover.lean`; Terra returned `Circular/Flip.lean`.
Primary verified them and added `ComponentSemantics.lean`, proving complete
component equality for connected orientations, extraction of the common
ascent factor, and `component_strict_eq_elementary_of_no_normal` for the
entire zero-normal family. Current ownership/checks are in `HANDOFF.md`.
