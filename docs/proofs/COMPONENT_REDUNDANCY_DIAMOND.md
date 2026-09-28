# Redundant edges across an actual diamond

2026-09-28. We identify exactly how redundant edges change across an
ordinary actual flip. This strengthens the paired diamond reduction and
gives a short proof of the unicyclic no-change lemma. It remains a local
identity: grouping its outputs into whole components is still required.

## The four selected relations

Let a<b<c, and let Z omit ab,ac,bc. Suppose the flip between

    P=Z+ac+ab       and       Q=Z+ac+bc

is actual. Thus Z has no directed path a→b, b→c, or a→c. Write

    B=Z+ac,                  T=Z+ab+bc.

We write Red(A) for the redundant selected edges of A. The ordinary
diamond, followed by deletion of its redundant long edge in the fourth
state, gives

    [P]+[Q]=[B]+[T],                                        (1)

where brackets denote either the strict coloring enumerator K or the
HRV elementary expression E. This is the same paired identity used in
[the flip-interaction note](COMPONENT_NN_FLIP_INTERACTIONS.md).

**Lemma.** The redundant-edge sets satisfy

    Red(B)=Red(P)∩Red(Q),
    Red(T)=Red(P)∪Red(Q).                                    (2)

All four sets in (2) consist of edges of Z: ac is a cover in P,Q,B,
and ab,bc are covers whenever they occur in these states.

For the second equality, T simulates ac by the path a→b→c. A bypass
at either endpoint therefore remains a bypass in T. Conversely, consider
a bypass in T for an edge e of Z. If it uses at most one of ab,bc, it
occurs in P or Q. If it uses both, they are consecutive on the path and
we replace them by ac, obtaining a bypass in both endpoints. This proves
the union identity.

For the first equality, every bypass in B also occurs in P and Q.
Suppose e=(u,v) is redundant in both endpoints but not B. Work throughout
with e deleted. The P-bypass must use ab, giving paths u→a and b→v
in Z−e. The Q-bypass must use bc, giving paths u→b and c→v in Z−e.
Combining the first prefix with ac and the second suffix gives a bypass
u→a→c→v in B−e, a contradiction. This proves the intersection identity.

## Deleting the redundant edges together

Deleting every redundant edge of a finite acyclic graph preserves its
reachability relation: its Hasse edges remain and generate that relation.
Put R=Red(P)∪Red(Q). Equations (1) and (2) therefore give

    [P]+[Q]=[B]+[T−R].                                      (3)

The state T−R has every selected edge covering. This is an identity for
both valuations with the same coefficients, and it retains any fixed
exterior satisfying the actual-flip cover tests.

If P is connected with cycle rank k, then T is connected with the same
edge count. Replacing ac by the path ab,bc preserves connectivity.
Deleting R preserves connectivity too. Consequently

    |Red(P)∪Red(Q)| ≤ k,                                   (4)

and T−R has cycle rank k−|R|. The other term B has one fewer selected
edge than P; it may be disconnected. If R is nonempty, both terms of
(3) have fewer selected edges. If R is empty, T has the same edge count
but smaller total edge length than either endpoint.

These decreases concern individual states. They do not establish a
recurrence in whole component sums. If ac or an edge of R is prescribed
strict, the corresponding term belongs to the diagram with those
strict corners deleted; normal-edge deletion stays in the same diagram.

## A transfer in cycle rank two

Suppose P is connected of cycle rank two, an edge e loses redundancy
across the flip, and a different edge f gains redundancy. The union
bound (4) forces

    Red(P)={e},              Red(Q)={f}.

Thus B has no redundant edge by (2). Moreover, the bypass of e in P
must use the deleted short ab. Hence ab lies on a cycle, and deleting
it leaves B connected. The three states P−e, Q−f and B are connected
unicyclic graphs with all selected edges covering; T−e−f is a tree.
We obtain the explicit reduction

    [P−e]+[Q−f]=[B]+[T−e−f].                               (5)

For example, in the complete natural graph on 0,1,2,3,4, retain 04 and
exchange 02 for 24:

    P={02,03,04,12,14,23},
    Q={03,04,12,14,23,24}.

Here e=03 loses redundancy through 02,23, while f=14 gains redundancy
through 12,24. Formula (5) is

    [{02,04,12,14,23}]+[{03,04,12,23,24}]
      =[{03,04,12,14,23}]+[{02,12,23,24}].                  (6)

The last term is the indicated four-edge tree.

With 04 strict, P and Q belong to a complete 84-state component. The
three unicyclic states in (6) all belong to one complete 80-state
component. The tree belongs to a four-state tree component after 04 is
deleted. These component memberships do NOT turn (6) into an identity
of the three whole component sums. Indeed, the proposed 84=80+4
component identity is false: the coefficient of e_5 is 28 on its left
and 18 on its right. Thus even here we must track multiplicities of the
emitted states before claiming reconstruction.

## Verification and scope

Astra independently derived (2), audited (3)–(5), and checked the bypass
arguments with the tested edge deleted. Primary checked these arguments
and the finite computations.

The Rust consumer checks (2) and the absence of redundant edges in T−R
across every actual directed flip of every selected forward graph on
four, five and six vertices: 52, 1,694 and 88,784 flips, respectively.
Among connected cycle-rank-two states, it finds 0, 22 and 764 directed
redundancy transfers. It also checks both valuations in (6), complete
component memberships in the example, and the failed whole-component
guess. The general lemma is proved above, not inferred from these checks.

Related Rust: `redundancy_transfer.rs`, reusing the existing `cover`,
`flip`, `components` and `valuations` consumer helpers. Frozen source and
receipts are under
`/lake-cache/ai-projects/requests/VerticalStripLLT/redundancy-transfer/`.
The final receipt is `diamond.jsonl`. No Lean or manuscript source is changed.
