# Component reconstruction with overlapping corners

2026-09-28. We extend the [four-edge calculation](COMPONENT_FOUR_EDGE_CASES.md)
to a five-vertex diagram with two overlapping strict corners. One correction
again completes two target components at once. This proves a further class
of component recurrences, including attached exterior components; the
general reconstruction problem remains open.

## The source and its NN image

We take area sequence (0,1,2,3,3), strict corners 03 and 14, and apply NN
at 1<2<4. Write L for this diagram and D for the diagram obtained by
deleting 14. Thus D has area sequence (0,1,2,3,2), with strict corner 03.
We write [P] for either K(P), the strict coloring enumerator, or E(P),
the HRV elementary expression, and sum this notation over sets of states.

For reproducible component names, we encode selected edges by binary masks,
starting with the least significant bit, in these orders:

    L: 01,02,03,12,13,14,23,24,34;
    D: 01,02,03,12,13,23,24,34.

C_m and D_m denote the complete components of L and D whose least masks
are m. The source components C_47 and C_63 have 34 and 32 states,
respectively. Among the connected non-tree components of L, these are
exactly those containing a state without a mixed directed cycle.
Here we reverse the strict edges when testing for a mixed directed cycle.

The canonical NN split from
[the redistribution note](COMPONENT_NN_REDISTRIBUTION.md), with q=12,
r=24 and adjacent swap σ=(1 2), already gives constant coefficients on
the target components for C_47:

    X(C_47)=X(D_71)+X(D_79)+X(D_85)+X(D_93)+X(D_102),   X=K,E.   (1)

For C_63, the coefficients are as follows. Components absent from the
table have coefficient zero on every state.

| Target component | Size | Coefficients of the NN image |
| --- | ---: | --- |
| D_79 | 16 | all 1 |
| D_93 | 3 | all 1 |
| D_95 | 9 | all 1 except state 246, which has 0 |
| D_125 | 3 | all 1 |
| D_157={157,181} | 2 | −1,0 |
| D_173 | 1 | −1 |
| D_230 | 1 | 1 |
| D_231 | 2 | all 1 |
| D_237 | 1 | 1 |

## Repairing the two incomplete components

We add the zero expression

    [246]−[181]=0.                                             (2)

In edge notation, this follows from

    {02,03,13,23,24,34}
      → {02,03,13,23,34}
      → {01,03,13,23,34}.

The first step deletes 24, implied by the path 2→3→4. The second step
swaps vertices 1 and 2. Both vertices are nonsinks, and the swap preserves
the order of the sinks. Hence both steps preserve K and E. Formula (2)
fills the missing positive coefficient in D_95 and the missing negative
coefficient in D_157 simultaneously.

We also have [237]=[173]: these states differ only by 24, again implied
by 23 and 34. Cancelling their contributions gives

    X(C_63)=X(D_79)+X(D_93)+X(D_95)+X(D_125)
               −X(D_157)+X(D_230)+X(D_231),       X=K,E.       (3)

All terms are whole components of the strictly smaller diagram D.
The correction changes both incomplete components together; repairing
one of their incident flips in isolation would not suffice.

## Checking that the target sets are complete

The following lists specify every target component in (1) and (3):

    D_71 = {71,77,78,86,92,101,108,116,197,204,212};
    D_79 = {79,87,94,103,109,110,118,124,
            199,205,206,214,220,229,236,244};
    D_85 = {85};
    D_93 = {93,117,213};
    D_95 = {95,111,119,126,207,215,222,246,252};
    D_102 = {102,198,228};
    D_125 = {125,221,245};
    D_157 = {157,181};
    D_230 = {230};
    D_231 = {231,238}.

There is a short way to check the lists without considering arbitrary
pairs of states. The restriction of D to 0,1,2,3 is the complete natural
diagram with strict corner 03. The selected status of 24 is invariant
under every flip. If 24 is absent, 34 is pendant and also invariant, so
we have precisely the four-vertex components with fixed 34-status.
If 24 is selected, all four-vertex flips remain available. The only
additional flip exchanges 23 and 34, retaining 24; whenever exactly one
of 23,34 is selected, this flip is available. Closing the four-vertex
components under these exchanges gives exactly the lists above.

For the source, the complete component lists used in the NN calculation
are recorded below. Applying the actual-flip cover criterion verifies
connectedness and closure, and substituting membership in the NN formulas
gives (1) and the displayed coefficient table.

    C_47 = {47,55,61,62,103,109,110,117,118,124,
            167,173,174,181,182,188,229,230,236,244,
            295,301,302,310,316,357,358,364,372,
            421,422,428,436,484};
    C_63 = {63,111,119,125,126,175,183,189,190,
            231,237,238,245,246,252,303,311,318,
            359,366,374,380,423,429,430,437,438,444,
            485,486,492,500}.

## Exterior components

Suppose these five consecutive vertices form the indicated block inside
an ordinary natural diagram. The exterior meets the block only at 0,4,
there is no exterior undirected path joining 0 to 4, and 03,14 remain
strict corners. Let Ω be any complete exterior component.

Every natural triangle lies in one part. A path leaving a part cannot
return to change a cover test, since such a return would supply an
exterior path between 0 and 4. Thus the full flip graph is the Cartesian
product of the two flip graphs. The NN swap fixes the exterior, as does
the swap in (2). The paths used to delete redundant edges remain present.

We may therefore retain an arbitrary exterior state in every step and
sum over Ω. Equations (1) and (3) hold with every component replaced by
its Cartesian product with Ω. Every resulting target is a complete
component in the corner-deletion diagram. This includes cyclic exterior
components. We evaluate on unions of states, counting each shared vertex
once; no product formula for polynomials at an articulation is used.

## Verification

The independent Astra audit checked the corrections, complete target
lists, and exterior extension. The Rust consumer checks the canonical
NN images and both valuations exactly. It also finds a local NN
certificate for each of the 24 source components of this five-vertex
diagram. The two displayed formulas concern the two components remaining
after the disconnected, tree and mixed-cycle reductions.

Related Rust: `nn_component_transport.rs`, `components` and `valuations`,
in the frozen external consumer under
`/lake-cache/ai-projects/requests/VerticalStripLLT/overlapping-corners/`.
The principal receipts are `canonical_pieces.jsonl` and
`local_certificates.jsonl`; the directory README records the source and
dependency provenance. No Lean or manuscript source is changed.
