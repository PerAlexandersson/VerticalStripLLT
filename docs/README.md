# Formalization documentation

## Current results and work

- [Ordinary completion audit](COMPLETION.md): unconditional expansion,
  positivity, degree, and alphabet compatibility.
- [Ordinary source and representation map](FORMALIZATION.md).
- [Circular completion audit](CIRCULAR_COMPLETION.md): full aggregate HRV
  formula, e-positivity, source correspondence and verification.
- [Verified circular results](CIRCULAR_STATUS.md).
- [Circular downstream work](CIRCULAR_GOALS.md): open component identity and
  manuscript exposition.
- [HANDOFF](../HANDOFF.md): current ownership, checks, remote task, and next step.

## Proof explanations

- [Reverse bounce search](proofs/CIRCULAR_BOUNCE_SEARCH.md).
- [Neutral-bounce termination](proofs/NEUTRAL_BOUNCE_TERMINATION.md).
- [Direct DN recurrence](proofs/CIRCULAR_DN_RECURRENCE.md).
- [DD propagation](proofs/CIRCULAR_DD_PROPAGATION.md): completed NN/DN elimination.
- [Direct ND](proofs/CIRCULAR_DIRECT_ND.md): the completed seven-relation proof.
- [Interior column reversal](proofs/CIRCULAR_COLUMN_REVERSAL.md): completed
  smaller-target reduction, residual transport, factorization and cancellation.
- [Earlier ND assembly](proofs/CIRCULAR_ND_ASSEMBLY.md): disjoint transport,
  cyclic intermediates and interior-restart exit accounting.
- [ND overlap obstruction](proofs/CIRCULAR_ND_OVERLAP.md) and
  [uniform root-overlap reduction](proofs/CIRCULAR_ND_ALIAS_REDUCTION.md).
- [Interior ND overlap](proofs/CIRCULAR_ND_INTERIOR_OVERLAP.md): historical
  obstruction analysis and the now-completed local restart route.

## Retained qualifications and provenance

- [Sufficient recurrence certificate](REDUCTION_CERTIFICATE.md): the proved
  route used by the ordinary expansion.
- [Restricted ordinary recurrence audit](RESTRICTED_BOUNCE_AUDIT.md): a separate
  open claim, unused by the proved ordinary expansion.
- [Circular flip interfaces](CIRCULAR_FLIPS.md): downstream component scope.
- [Diamond straightening audit](proofs/DIAMOND_STRAIGHTENING_AUDIT.md):
  exact obstruction, auxiliary-state repair and exterior-swap correction.
- [Sink-deletion companion](proofs/COMPONENT_SINK_BRANCHING.md): proved
  reconstruction, proposed HRV branching, and its implication for components.
- [Source-deletion companion](proofs/COMPONENT_SOURCE_BRANCHING.md): preserves
  remaining HRV and reduces the gap to a source/fiber cancellation identity.
- [Movable leaf packets](proofs/COMPONENT_LEAF_PACKETS.md): proved packet
  cancellation and star transport for one coefficient in every full component.
- [Attached chains](proofs/COMPONENT_BRIDGE_PACKETS.md): five-flip attachment
  transport, telescoping source cancellation, and the open marked-ideal identity.
- [Ambient reduction](proofs/COMPONENT_AMBIENT_REDUCTION.md): exact reduction
  to complete circular diagrams, the ordinary reduction for zero-winding
  components, and the stronger projected-cover companion.
- [Component induction brainstorming](proofs/FLIP_COMPONENT_INDUCTION.md):
  exact corner branching, always-redundant corner deletion, and repaired transfers.
- [Active corner companion](proofs/COMPONENT_ACTIVE_CORNERS.md): the open ordinary
  connectivity lemma that would isolate components from aggregate coefficients.
- [Aristotle ledger](ARISTOTLE.md): request IDs, candidates, and local verification.
- [Historical plans](archive/completed-plans/README.md): superseded implementation
  outlines and the original architecture audits. They are not active work lists.
- [Component research handoff archive](archive/flip-component-checkpoints-through-c6305a0.md):
  earlier checkpoints, failed approaches, and completed consultation provenance.

Completed plans no longer duplicate the active agenda. The Lean declarations
and local verification establish the results; explanatory notes record the
mathematical arguments and their precise remaining boundaries.
