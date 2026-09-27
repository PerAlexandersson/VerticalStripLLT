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
- [Flip-component proof status](FLIP_COMPONENT_STATUS.md): the current proof
  map, proved reductions, remaining connectivity lemma, and circular scope.
- [HANDOFF](../HANDOFF.md): current ownership, checks, remote task, and next step.

## Completed aggregate proof explanations

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

## Component research: main route

Start with [the proof-status map](FLIP_COMPONENT_STATUS.md). The detailed
notes below each own one argument; process status lives in the handoff.

- [Circular flip interfaces](CIRCULAR_FLIPS.md): exact downstream target and
  locally verified foundations.
- [Component recurrence reductions](proofs/FLIP_COMPONENT_INDUCTION.md):
  the exact transport certificate, author case table, corner branching,
  always-redundant corner deletion, and repaired transfers.
- [Corner differences](proofs/COMPONENT_CORNER_DIFFERENCES.md): signed recurrences
  in whole smaller components, mixed-cycle cancellation, relative absorption,
  and the circular restriction on arbitrary deletion.
- [Exact HRV differences](proofs/COMPONENT_HRV_DIFFERENCES.md): local conditions
  for every signed map coefficient, the component counting refinement, and
  obstructions to preserving each vertex's color.
- [Strict-chain normalization](proofs/COMPONENT_CHAIN_NORMALIZATION.md): actual
  flip paths to a fixed reference order, deterministic representatives,
  connected fibers, their coloring sums, and crossing-corner slides.
- [Anchor slides](proofs/COMPONENT_ANCHOR_SLIDES.md): exact cover tests,
  consecutive-chain connectivity, and signed smaller-area corrections for
  both valuations; whole-component regrouping remains open.
- [Mixed closure](proofs/COMPONENT_MIXED_CLOSURE.md): normals implied by mixed
  reachability preserve both alternating valuations; acyclic closure fibers
  are Boolean intervals, giving further exact relations for regrouping.
- [DN component completion](proofs/DN_COMPONENT_COMPLETION.md): explicit
  component grouping, proved recurrence transport, and the remaining local
  isolation assertion.
- [Active corner companion](proofs/COMPONENT_ACTIVE_CORNERS.md): coefficient
  isolation, the articulation counterexample, and the open refined uniqueness.
- [Endpoint recovery and gluing](proofs/COMPONENT_ENDPOINT_GLUING.md): proved
  marked aggregate identities and separate ascent variables at articulation blocks.
- [Tree connectivity](proofs/COMPONENT_TREE_CONNECTIVITY.md): proved corner
  leaf normalization and connectivity of all trees with a fixed envelope.
- [Connected aggregate and forest semantics](proofs/COMPONENT_CONNECTED_AGGREGATE.md):
  partition inversion isolates the tree coefficient and proves every forest component.
- [Ambient reduction](proofs/COMPONENT_AMBIENT_REDUCTION.md): complete circular
  ambient diagrams, the balanced-to-ordinary reduction, and StrongSrc.
- [Winding lattice](proofs/COMPONENT_WINDING_LATTICE.md): invariant cycle data
  and exact reduction of unbalanced components to primitive circular components.
- [Exact winding aggregate](proofs/COMPONENT_LATTICE_AGGREGATE.md): compatible-edge
  filtering and finite-poset inversion, with a checked obstruction to component isolation.

## Component research: auxiliary routes and obstructions

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

## Qualifications and provenance

- [Sufficient recurrence certificate](REDUCTION_CERTIFICATE.md): the proved
  route used by the ordinary expansion.
- [Restricted ordinary recurrence audit](RESTRICTED_BOUNCE_AUDIT.md): a separate
  open claim, unused by the proved ordinary expansion.
- [Aristotle ledger](ARISTOTLE.md): request IDs, candidates, and local verification.
- [Historical plans](archive/completed-plans/README.md): superseded implementation
  outlines and the original architecture audits. They are not active work lists.
- [Component research handoff archive](archive/flip-component-checkpoints-through-c6305a0.md):
  earlier checkpoints, failed approaches, and completed consultation provenance.
- [Handoff through endpoint recovery](archive/flip-component-handoff-through-ffa23fd.md)
  and [earlier Aristotle ledger](archive/aristotle-ledger-through-endpoint-recovery.md):
  historical snapshots, not current task status.
- [Handoff through DN transport](archive/flip-component-handoff-through-dn-transport.md):
  winding and recurrence research chronology before component completion.

Completed plans no longer duplicate the active agenda. The Lean declarations
and local verification establish the results; explanatory notes record the
mathematical arguments and their precise remaining boundaries.
