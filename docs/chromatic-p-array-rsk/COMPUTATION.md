# Bounded chromatic P-array RSK experiment

## Result

The standalone Rust prototype in
`experiments/chromatic-p-array-rsk/` exhausts every natural unit interval
order through rank five.  For every packed content and every q-degree it
checks both the coefficient identity and the explicit alternating-path map.
Every produced image reverses to the original coloring.

| rank | orders (KP-eligible) | packed colorings (KP-eligible) | target pairs | longest trace |
|---:|---:|---:|---:|---:|
| 1 | 1 (1) | 1 (1) | 1 | 0 |
| 2 | 2 (2) | 5 (5) | 5 | 2 |
| 3 | 5 (5) | 47 (47) | 47 | 8 |
| 4 | 14 (14) | 671 (671) | 671 | 26 |
| 5 | 42 (41) | 12,977 (12,713) | 12,977 | 64 |

Here a trace event is one application of either signed involution.  The
totals are 64 posets and 13,701 source colorings.  Of these, 63 posets and
13,437 colorings are in the Kim--Pylyavskyy avoidance class.  The unique
excluded rank-five order is `P_(3,1,1),5`.  The deterministic trace checksum
is 345,657; this is only a regression fingerprint, not a mathematical
invariant.

Run the complete check with

```text
CARGO_TARGET_DIR=/cargo-target/ai-projects \
  cargo run --release \
  --manifest-path experiments/chromatic-p-array-rsk/Cargo.toml
```

The unit tests exhaust ranks at most four and separately assert the minimal
LGV obstruction.  The rank-five check remains in the executable so the usual
test loop stays short.

## Implemented map and certificate

For a coloring of packed content `mu`, the program performs the following
reversible steps.

1. Color complement changes `asc` into `des`; odd-component color switches
   restore the original ordered content.
2. Odd-component switches normalize `mu` to `mu+`.
3. The canonical positive fixed state of the finite reverse-inverse-Kostka
   matching is attached.
4. The conjugated Shareshian--Wachs involution and that matching alternate
   until the state is fixed by Shareshian--Wachs.
5. The final state is a P-tableau and an ordinary semistandard tableau of
   content `mu`.

A state stores `(A, lambda, pi, Q)`.  A Shareshian--Wachs event stores its
selected row and column and the subsequent normalization word.  An
inverse-Kostka event stores `nu` and both endpoint triples.  These data are a
reversible certificate: the executable applies every Shareshian--Wachs move
twice as an assertion, applies every matching move twice as an assertion, and
runs the whole trace backwards from every target.

The bounded prototype deliberately uses lexicographic matching in the
reverse-inverse-Kostka fiber.  This is an explicit finite bijection, but it is
not presented as a satisfactory local generalized RSK.  Allen--Celano--Mason
Algorithm 5.4 can replace this oracle using the variable change recorded in
`SIGNED_SETS.md`; that import is the next algorithmic step.

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
