# Constructive chromatic P-array RSK map

## Result

The standalone Rust prototype in
`experiments/chromatic-p-array-rsk/` exhausts every natural unit interval
order through rank five.  For every packed content and every q-degree it
checks both the coefficient identity and the explicit alternating-path map.
Every produced image reverses to the original coloring.

| rank | orders (KP-eligible) | packed maps | one-empty-color maps | inverse-Kostka endpoints | longest trace |
|---:|---:|---:|---:|---:|---:|
| 1 | 1 (1) | 1 | 2 | 1 | 0 |
| 2 | 2 (2) | 5 | 14 | 4 | 2 |
| 3 | 5 (5) | 47 | 170 | 16 | 10 |
| 4 | 14 (14) | 671 | 2,966 | 76 | 30 |
| 5 | 42 (41) | 12,977 | 67,682 | 376 | 120 |

Here a trace event is one application of either signed involution.  The
totals are 64 posets and 13,701 source colorings.  Of these, 63 posets and
13,437 colorings are in the Kim--Pylyavskyy avoidance class.  The unique
excluded rank-five order is `P_(3,1,1),5`.  The deterministic trace checksum
is 659,062; this is only a regression fingerprint, not a mathematical
invariant.

Run the complete check with

```text
CARGO_TARGET_DIR=/cargo-target/ai-projects \
  cargo run --release \
  --manifest-path experiments/chromatic-p-array-rsk/Cargo.toml
```

The unit tests exhaust ranks at most four, including weak contents and the
transported crystal operators, and separately assert the minimal LGV
obstruction.  The rank-five check remains in the executable so the usual test
loop stays short.

## Implemented map and certificate

For a coloring of weak content `mu` in a fixed finite alphabet, the program
performs the following reversible steps.

1. Color complement changes `asc` into `des`; odd-component color switches
   restore the original ordered content.
2. Odd-component switches normalize `mu` to `mu+`.
3. The canonical positive fixed state of the reverse-inverse-Kostka
   involution is attached.
4. The conjugated Shareshian--Wachs involution and the local
   Allen--Celano--Mason involution alternate until the state is fixed by
   Shareshian--Wachs.
5. The final state is a P-tableau and an ordinary semistandard tableau of
   content `mu`.

A state stores `(A, lambda, pi, Q)`.  A Shareshian--Wachs event stores its
selected row and column and the subsequent normalization word.  An
inverse-Kostka event stores `nu`, both endpoint triples, and every local
Algorithm 4.2 or Algorithm 5.1 move.  These data form a reversible trace: the
executable applies each local involution twice, applies every
Shareshian--Wachs move twice, and runs the whole map backwards from every
target.

The inverse-Kostka move first applies ordinary Bender--Knuth involutions to
change the tableau content from `mu` to `mu+`.  It then sets `sigma=pi^-1`
and uses

```text
Delta_j = lambda_j - j + sigma(j),
Delta_pi(i) = alpha(lambda,pi)_i.
```

Algorithm 4.2 moves one entry between rows of the resulting immaculate
tableau, inserting or deleting a row when required.  If the result is not
semistandard, Algorithm 5.1 applies its bad-cell tail switch, and the two
moves alternate as in Algorithm 5.4.  At the next semistandard endpoint we
invert `sigma`, undo the ordinary Bender--Knuth involutions, and return a
triple of the original kind.  Tunnel-hook diagrams are not extra state:
their shape and permutation determine them uniquely.

## Weak contents and classical crystal operators

Allowing zero parts is necessary for a crystal on a fixed alphabet.  The
color complement, odd-component switches, and ordinary Bender--Knuth maps all
remain valid with empty color classes.  The implementation therefore accepts
a specified alphabet size rather than inferring it from the support.

The finite check inserts an empty color class in every possible position of
every packed coloring, giving 67,682 additional rank-five maps.  For every
such state it also applies the ordinary tableau Kashiwara operators to `Q`
and transports them through the bijection.  The transported operators are
partial inverses, preserve properness and `asc`, change the weight by the
corresponding simple root, and map forward to the same `T` with the altered
`Q`.  Hence these are the ordinary normal type-A operators transported by
the constructed bijection, rather than Ehrhard's weaker partial-inverse
operators.

The coloring-level functions are `coloring_e` and `coloring_f`.  They compute
`Phi`, apply the ordinary signature rule to `Q`, and run the reversible map
backward.  The check now also computes every `epsilon_i` and `phi_i`, verifies

```text
phi_i - epsilon_i = wt_i - wt_(i+1),
```

and identifies every highest-weight state with the row-constant
highest-weight tableau.  The finite totals are:

| rank | checked weak states | `f_i` edges | string checks | highest-weight states |
|---:|---:|---:|---:|---:|
| 1 | 2 | 1 | 2 | 1 |
| 2 | 14 | 11 | 26 | 4 |
| 3 | 170 | 189 | 458 | 23 |
| 4 | 2,966 | 4,277 | 10,418 | 188 |
| 5 | 67,682 | 120,659 | 292,322 | 1,849 |

For every natural unit interval order through rank five, the program also
constructs the complete fixed-alphabet graph with `k=n`.  It checks that an
edge never changes `(lambda,T)`, that every fixed-`T` fiber is connected, and
that it has a unique highest-weight vertex.  Thus the computed graph has the
component decomposition

```text
Col_k(P) = disjoint union over (lambda,T) of B_k(lambda).
```

| rank | full graph vertices | directed edges | components |
|---:|---:|---:|---:|
| 1 | 1 | 0 | 1 |
| 2 | 6 | 2 | 4 |
| 3 | 81 | 68 | 23 |
| 4 | 1,780 | 2,322 | 188 |
| 5 | 55,125 | 96,968 | 1,849 |

There is a direct formula for every component anchor.  If `T` is regarded as
its row coloring, the highest-weight coloring is `R_lambda^{-1}(T)`, where
`R_lambda` is the ascent-to-descent orientation map.  At this endpoint the
inverse-Kostka state is already fixed, so the reverse map does not traverse an
alternating path.  The complete graph check verifies this formula for all
1,849 rank-five components.

To export a graph in Graphviz DOT format, pass a one-based Hessenberg code and
an alphabet size.  For example:

```text
CARGO_TARGET_DIR=/cargo-target/ai-projects \
  cargo run --release \
  --manifest-path experiments/chromatic-p-array-rsk/Cargo.toml \
  -- --dot 1,2,3 2 > /tmp/chain3-k2.dot
```

## What the first graphs say about an intrinsic rule

The current transport is genuinely global.  The exhaustive miner gives the
following smallest examples, written here with ordinary one-based colors.

- On the three-element chain, `f_1(112)=221`; one operator changes all three
  vertices.
- On the same chain with three colors, `f_1(132)=322`; a vertex carrying the
  third color moves, so the operation is not confined to colors 1 and 2.
- On the four-element chain, `1134` and `1143` have weight `(2,0,1,1)`, ascent
  zero, and the same labeled restriction to colors 1 and 2, but
  `f_1(1134)=2134` whereas `f_1(1143)=4321`.

The last pair rules out any description based only on the induced subgraph on
the two active colors, even after weight and ascent are supplied.  It does not
rule out a useful intrinsic global description.  The promising candidates are
a word-level bracketing on a canonical global reading word, a growth diagram,
or a compressed version of the signed alternating-path certificate.  Any such
proposal must reproduce these three examples.

## Crystal reflections and braid relations

The prototype also exposes the total simple reflection

```text
S_i = f_i^(wt_i-wt_(i+1))  if wt_i >= wt_(i+1),
S_i = e_i^(wt_(i+1)-wt_i)  otherwise.
```

Equivalently, it reverses the `i`-string of `Q` and transports the result back
to the coloring.  Through rank five, all 169,016 adjacent braid tests and all
167,155 distant-commutation tests pass.  Involution, weight swap, properness,
and ascent preservation are checked at every one of the 226,008
`(coloring,i)` states.

Three superficially similar operations are distinct:

| comparison through rank five | agreements | total |
|:--|--:|--:|
| crystal reflection versus SW odd-component switch | 169,220 | 226,008 |
| crystal reflection versus tableau Bender--Knuth | 199,316 | 226,008 |
| transported tableau Bender--Knuth versus SW switch | 176,690 | 226,008 |

The first reflection/SW difference is the two-element chain: the reflection
fixes `12`, whereas the odd-component switch gives `21`.  The SW switches fail
7,236 of 169,016 adjacent braid tests.  Transported tableau Bender--Knuth
switches fail 13,330; this is why content-swapping Bender--Knuth involutions
must not be identified with the genuine crystal Weyl action.

The transported reflections are still global.  The first move involving an
outside color is, on the four-element chain,
`S_2(1223)=2331`.  At rank five there are colorings with the same content,
ascent, and active two-color restriction but different reflected restrictions.

We also tested the most immediate intrinsic replacement.  Order the odd
components of the active two-color graph, record the majority color in each,
cancel opposite signs, and flip only the excess unmatched components.  The
four combinations of increasing/decreasing component order and the two
cancellation orientations have no braid failure through rank five.  This is
misleading: as Astra's independent audit observed, the first genuinely
constraining three-color content is `(3,2,1)` at rank six.  Every variant then
has 38 failures among the 1,296 proper colorings of that content over all 132
orders, and 228 failures among all 16,020 rank-six braid tests.  For increasing
component order and `+-` cancellation, the first certificate is

```text
121321 --S_1--> 122321 --S_2--> 133231 --S_1--> 133232,
121321 --S_2--> 131321 --S_1--> 232321 --S_2--> 233231,
P=(1,2,4,5,6,6).
```

This exact delayed obstruction explains why low-rank experimentation with
odd-component pairings is unusually deceptive.  Astra independently
implemented Ehrhard's alignment and weak operators; their reflections agree
with this component-signature rule in all 2,592 single-reflection checks on
the rank-six `(3,2,1)` orbit.  Thus the same witness is also a concrete braid
failure for Ehrhard's weak, non-normal operators.

For involutions, the braid relation is equivalent to
`D=(R_1 R_2)^3=id`.  On this witness the defect has the exact cycle

```text
233231 -> 133232 -> 233213 -> 233231
```

and fixes the other 19 proper colorings of weight `(1,2,3)`.  Of these 22
colorings, 11 have ascent one and 11 have ascent two; the moved three-cycle
has ascent one.  The orbit generated from `121321` by `R_1,R_2` is an
18-cycle of ascent one, with three colorings at each of the six permutations
of weight `(3,2,1)`.
Thus the weak action is a three-sheeted cover of the Coxeter hexagon at the
first obstruction.

Consequently there is no single global conjugation taking every `R_i` to the
corresponding genuine `S_i`: conjugation would preserve the failed braid
relation.  A repair must be root-dependent or must enlarge the state by a
sheet label.

Component data for the two roots separately does not identify the sheet.  On
the same order, `132121` and `312121` have weight `(3,2,1)`, ascent one, and
identical complete ordered colored component words for both pairs:

```text
colors 1/2:  1 | 2121
colors 2/3:  3 | 2 | 2
```

Nevertheless `D(132121)=123121`, while `D(312121)=312121`.  The inputs differ
only by swapping colors 1 and 3 on the two isolated initial vertices.  Thus a
rule built from separate component sizes, majorities, or even their full
colored words misses the cross-root interleaving needed to control holonomy.

Nor is the sheet number uniformly three.  Over all rank-six orders and all
1,296 proper colorings of content `(3,2,1)`, the cycle inventory of `D` is

```text
fixed points: 1,258
3-cycles:        11
5-cycles:         1
```

The 5-cycle belongs to the connected path `P=(2,3,4,5,6,6)`:

```text
121321 -> 132121 -> 212131 -> 312121 -> 213121 -> 121321.
```

Its full weak rank-two orbit is a 30-cycle, five points over each vertex of
the Coxeter hexagon.  In particular, a universal mod-three sheet label cannot
repair the weak action.

This five-cycle is the first member of an unbounded path family.  For the path
on `n=2a` vertices, let `A_m` be the alternating `1/2` word of length `m`
ending in `1`.  The fixed-content/ascent fiber

```text
weight=(a,a-1,1), asc=a-1
```

consists exactly of `w_j=A_(j-1) 3 A_(2a-j)` for `1 <= j < 2a`.  On this
fiber `D(w_j)=w_(d(j))`, where

```text
d(1)=2a-3,                         d(3)=4,
d(j)=j-4       for odd j>=5,
d(j)=j+4       for even 2<=j<=2a-6,
d(2a-4)=2a-1,                      d(2a-2)=2.
```

For odd `a`, this is one cycle of length `2a-1`.  For even `a`, the cycle
lengths are `a/2,a-1,a/2`.  A short proof uses vertex reversal followed by
the color complement `1<->3`: this involution conjugates `R_1` to `R_2`, so
the displayed permutation is the square of its composition with
`R_2 R_1 R_2`.  Direct Rust checks verify both the exact fiber and every
clause of the formula for `3 <= a <= 10`.  Thus weak braid holonomy has
unbounded order, although this does not assert unbounded order for `C_i`.

### The correction between the two reflections

Write `R_i` for the increasing-order, `+-`-cancellation component reflection
and define `C_i=S_i R_i`, with the rightmost map applied first.  Then `C_i`
preserves weight and ascent, and

```text
S_i(x) = C_i(R_i(x)),
C_i^(-1) = R_i S_i,
R_i C_i R_i = S_i C_i S_i = C_i^(-1).
```

The correction is sparse, is not an involution, and already has cycles of
length up to 20.  Its complete rank-five census is:

```text
fixed states:          197,212 / 226,008
same insertion shape: 207,046 / 226,008
same insertion T:     200,248 / 226,008
cycle lengths:        1,2,3,4,5,6,7,8,9,10,11,12,13,15,16,20
```

The first nontrivial example is already the three-element chain.  In
one-based colors,

```text
C_1: (112 121 211)(122 212 221).
```

Thus this correction measures not only a poset-specific braid defect but also
the gauge of the chosen signed bijection: the present `Phi` does not reduce to
ordinary RSK on a chain.

More precisely, for adjacent roots `i,j`, set `D=(R_i R_j)^3`, use
`^g H=g H g^(-1)`, and put

```text
L = C_i (^R_i C_j) (^(R_i R_j) C_i),
M = C_j (^R_j C_i) (^(R_j R_i) C_j).
```

Expanding `S_i=C_i R_i` shows that the genuine braid relation is exactly
`L D=M`, or `D=L^(-1) M`.  The correction cocycle therefore cancels the weak
rank-two holonomy.  Also `T(C_i(x))=T(R_i(x))` exactly, because `S_i`
preserves the insertion tableau.  This separates crossing to the weakly
reflected insertion component from gauge motion within that component.

To test whether inverse-Kostka traversal completely explains the correction,
the program records whether the forward traces of `x`, `R_i(x)`, and `C_i(x)`
contain an inverse-Kostka event:

| IK on `x` | IK on `R_i(x)` | IK on `C_i(x)` | states | nontrivial `C_i` |
|:--:|:--:|:--:|--:|--:|
| no | no | no | 87,090 | 3,260 |
| yes | no | no | 4,906 | 4,906 |
| no | yes | yes | 4,906 | 4,906 |
| yes | yes | yes | 129,106 | 15,724 |

No other mask occurs through rank five.  In particular, changing the recorded
presence/absence of an inverse-Kostka event always accompanies a correction
in this census, but 3,260 corrections occur with no inverse-Kostka event at
any endpoint.  The smallest is `001 -> 010` on the three-element chain.
Therefore inverse Kostka is a major bottleneck, but the orientation,
normalization, and nonclassical chain gauge also contribute.

The restriction to four masks is forced rather than a separate experimental
pattern.  A forward path contains an inverse-Kostka step exactly when its
terminal shape is not the decreasing rearrangement of its content.  Moreover,
`R_i(x)` and `C_i(x)` have the same sorted content and the same insertion
tableau, so their two flags agree.  A more discriminating experiment must use
the ordered local `psi/theta` word, not merely the presence of such a step.

The refined certificate needs less data than that experiment initially
recorded.  Flatten all inverse-Kostka edges to the detailed ordered
`psi/theta` word: a `psi` letter stores its source and target rows and
insertion/deletion flags, while a `theta` letter stores its row and column.
Discard intermediate shapes, edge boundaries, and all SW events.  Its
rank-five census gives:

```text
full-alphabet colorings tested:                         56,993
collisions of (weight, T, detailed IK word):                  0
nontrivial C_i preserving the detailed IK word:           5,780
  of which the word is nonempty:                          2,520
nontrivial C_i preserving both T and that word:                0
```

For comparison, 3,036 of the 28,796 nontrivial correction states preserve
`T`, while 25,760 cross to another insertion tableau.  Neither coordinate
alone determines a correction, but their pair is formally reversible.  Start
from the row-constant normalized tableau for the sorted content and replay the
recorded row moves and tail switches.  This reconstructs the terminal
`(lambda,Q)` because intervening SW moves change only the permutation
coordinate; undoing content normalization gives `Q`, and `(T,Q)` determines
the coloring.  The Rust implementation asserts this replay identity for all
56,993 tested colorings.  What remains unknown is an intrinsic update rule for
the word under `S_i`.

The obvious standardization shortcut also fails.  Splitting equal colors into
consecutive labels in increasing vertex order first fails for the two-element
chain and the coloring `11`.  Decreasing vertex order survives rank two but
first fails for the three-element chain: `111` standardizes to `321`, while
its image changes from shape `(3)` to shape `(2,1)` rather than retaining `T`
and merely standardizing `Q`.  Thus the present map is not obtained by
destandardizing a permutation-level correspondence.

The exact source of the global behavior can be narrowed further.  Let `F_i`
act only on `Q` in the common signed set.  It commutes with the conjugated
Shareshian--Wachs involution: that involution leaves `Q` unchanged, and its
move is determined by `(A,lambda,pi)`.  It need not commute with the
reverse-inverse-Kostka involution `I`.  A census over all positive contents
through rank five gives:

| rank | `(state,i)` tests | defects | definedness defects | unequal-value defects |
|---:|---:|---:|---:|---:|
| 1 | 0 | 0 | 0 | 0 |
| 2 | 3 | 2 | 2 | 0 |
| 3 | 24 | 10 | 10 | 0 |
| 4 | 170 | 55 | 46 | 9 |
| 5 | 1,120 | 309 | 226 | 83 |

The first defect is the rank-two inverse-Kostka cancellation with
`nu=(2)` and `mu=(1,1)`.  For the positive state

```text
u = (lambda=(2), pi=id, Q=[1 2]),
```

`F_1(I(u))` is undefined, whereas `F_1(u)` has `Q=[2 2]` and is fixed by
`I` in the new content `(0,2)`.  Thus the most focused candidate for a
compressed intrinsic algorithm is a marked trace: carry the unmatched cell
of `Q` backward freely across Shareshian--Wachs events, and expand only at
inverse-Kostka events where `F_i` and `I` fail to commute.  The next finite
classification should sort these defects by their Allen--Celano--Mason
`psi/theta` event words and test whether the required correction has bounded
local support.

## Smallest obstruction to a bare LGV tail switch

The failure occurs already at rank two, independently of the poset.  Take
content `mu=(1,1)` and complete-homogeneous index `nu=(2)`.  The entire
reverse-inverse-Kostka fiber consists of two states:

| sign | `lambda` | `pi` | `alpha(lambda,pi)` | `Q` |
|:---:|:---:|:---:|:---:|:---:|
| + | `(2)` | `id` | `(2,0)` | the row `1 2` |
| - | `(1,1)` | `(12)` | `(0,2)` | the column `1 / 2` |

This is the cancellation

```text
K_(2),(1,1) [h_(2)]s_(2)
+ K_(1,1),(1,1) [h_(2)]s_(1,1) = 1 - 1 = 0.
```

An ordinary LGV first-intersection tail switch changes the endpoint
permutation inside one fixed Jacobi--Trudi determinant, hence preserves
`lambda`.  The required two states have different `lambda`.  Therefore no
choice of first intersection or tail-switch ordering can pair this fiber.
This does not obstruct a Garsia--Milne construction; it shows exactly why a
second, reverse-inverse-Kostka involution is necessary.

For the chain poset, the complete nontrivial Garsia--Milne certificate in
this fiber can be written without abbreviations.  Attach `A=[1 2]` to the
two displayed states and call them `u` (positive) and `v` (negative).  Let

```text
w=(A=[2]/[1], lambda=(1,1), pi=id, Q=[1]/[2]),
z=(A=[1]/[2], lambda=(1,1), pi=id, Q=[1]/[2]).
```

If `I` is reverse-Kostka cancellation and `J` is conjugated
Shareshian--Wachs, then

```text
I: u <-> v,  I(w)=w, I(z)=z;
J: v <-> w,  J(u)=u, J(z)=z.
```

Hence the sole nontrivial path is `w --J--> v --I--> u`; `z` is fixed by
both involutions.  All four states have degree zero.

There is also a literal same-cut failure in this rank-two state.  Use the
chain poset and normalized array `[1 2]`.  For `lambda=(1,1)` and
`pi=(12)`, denormalization gives `[]/[1 2]`.  Shareshian--Wachs selects the
first cell and moves the odd singleton tail, whereas applying the same cut
to `Q=[1]/[2]` gives `[]/[2 1]`.  The result is neither partition-shaped nor
row-weakly increasing.

A more permissive proposal might swap all tails, rather than insist that the
same operation remain inside the semistandard fiber.  Its first q-obstruction
occurs at rank four.  In one-based notation take

```text
m=(1,3,3,4),  G={{2,3}},  lambda=nu=(2,2),  pi=id,
A=[2 4]/[1 3],  Q=[1 1]/[2 2].
```

The selected cut is the first cell.  Its tail graph consists of the even
component `{2,3}` and the odd singleton `{4}`.  Shareshian--Wachs leaves the
even component fixed and gives `[2]/[1 3 4]`, retaining `des=0`.  Swapping
all tails gives `[3]/[1 2 4]`, whose `des` is 1.  Thus the all-tail move is
not q-preserving.  No such admissible example exists through rank three:
an even tail component would force row lengths `(1,2)`, which makes the
shifted determinant parts repeat.

## Kim--Pylyavskyy oracle

On their pattern-avoidance class, Kim--Pylyavskyy supplies an independent
map, including repeated colors after block standardization and recording
tableau destandardization.  The precise extension and statistic comparison
are recorded in `SIGNED_SETS.md`.  The current executable checks the same
source and target fibers on every rank-five poset but does not reimplement
their substantial insertion algorithm.  The traced inverse-column insertion
in `/workspace/rust/sym-poly/core/src/p_rs.rs` was inspected as a read-only
oracle component; it implements Algorithm 2, not the full forward P-RS map.
