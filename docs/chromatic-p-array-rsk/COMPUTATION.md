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
