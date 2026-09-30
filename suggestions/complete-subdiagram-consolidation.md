# Consolidate complete-diagram restriction after P4

`CompleteRestriction.lean` implements deletion of the last vertex;
`CompleteSubdiagram.lean` now implements restriction along any increasing
vertex embedding. Their selected-relation reconstruction proofs overlap.
Maintaining both implementations could cause small fixes to diverge.

After the interval/chord interfaces settle, retain the existing prefix API
but define it through the general construction at `Fin.castSuccOrderEmb`.
Prove that its exterior is exactly the top-edge set, and recheck
`CompleteChain` plus the focused axiom audit. This is a maintenance proposal,
not a reason to delay the remaining diagram proof.

P4 is now complete. `CliqueRestriction.lean` adds the same restriction and
exterior reconstruction for an arbitrary forward ambient diagram, lifting
through `D.undecorated` and restoring strict markings. Include it in a later
consolidation review: retain the existing declaration shapes, specialize the
general construction for complete ambient diagrams, and check the selected
relations and count interfaces before replacing their older implementations.
