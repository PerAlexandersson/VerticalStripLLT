# Local Kim--Pylyavskyy insertion and its first corrections

This note records the exact Kim--Pylyavskyy column algorithm, its inverse,
and the finite corrections found through rank six.  The primary source is
paper-cache 297, D.~Kim and P.~Pylyavskyy, *Robinson--Schensted correspondence
for unit interval orders*, arXiv:2003.12123v2.  We use Algorithms 1--3,
Proposition 5.6, Theorem 6.1, and Examples 7.9--7.11.

The result has two levels.

- On the avoidance class in Theorem 6.1, the published algorithm is a
  reversible insertion map.
- For all natural unit interval orders through rank six, a finite guarded
  correction gives a reversible bijection onto pairs of tableaux.  The
  rank-six guards do not yet give an all-rank insertion rule.

## 1. Conventions and the column step

Words are stored as ((a_m,\dotsc,a_1)) and scanned from right to left.  A
column is read from bottom to top, but the mutable column in the algorithm is
indexed from top to bottom as

\[
  d_1 <_P d_2 <_P \dotsb <_P d_\ell.
\]

Empty word positions are denoted by (\infty).  Numerical comparisons and
comparisons in (P) have different roles.  Given the next finite letter
(a_p), first choose

\[
  r=\max\{i: d_i<a_p\},
  \qquad d_0=-\infty,
\]

using the natural order on the labels.  If (r=0) or (d_r<_P a_p), then
(a_p) either extends the column or replaces (d_{r+1}), which is emitted
in the same word position.

Suppose instead that (d_r) and (a_p) are incomparable.  Choose the
lexicographically largest pair ((h,q)), maximizing (h) first, such that

\[
  a_p<a_{p+1}<\dotsb<a_{p+q}
\]

and

\[
  \{d_r,\dotsc,d_{r+h},a_p,\dotsc,a_{p+q}\}
\]

is a (P)-ladder.  A sorted set (y_1<\dotsb<y_s) is a ladder precisely
when consecutive elements are incomparable and (y_i<_P y_j) for
(j\geq i+2).  Thus checking consecutive incomparability alone is not
sufficient.

If (a_{p+q}<d_{r+h}), the entire source block passes through.  Otherwise,
the algorithm replaces the selected column interval by the appropriate
source letters and emits the displaced letters in their original positions.
The Rust implementation records the source interval, the case, the column
before and after the step, and the emitted letters.

Algorithm 3 starts every column pass with an empty column.  The recording
column consists of the scan positions at which a finite input becomes an
empty output, namely the positions where a letter extends the column.  These
labels are scan positions, not the identities of the inserted letters.

## 2. The published inverse

Algorithm 2 modifies the same column step at selected empty positions.  At
such a position, it removes the top entry of the active column and places it
in the word.  To reverse a column pass, one reverses positions, complements
labels in ([n]), works in the dual poset, and selects the complemented
recording positions for these removals.  The resulting column must be empty.
Repeating this from the last column to the first recovers the word.

This inverse remains useful outside the avoidance class.  Proposition 5.6
gives reversibility of an individual column calculation without assuming
that the assembled columns form tableaux.  In the implementation, a
nonempty residual column or an empty final word position is returned as a
failure rather than being discarded.

To insert proper colorings, we use the standardization from `DIRECT_MAP.md`.
The recording convention in Theorem 6.1 satisfies

\[
  \operatorname{Des}(Q)
  =\{n-i:i\in\operatorname{Des}_P(w)\}.
\]

We first apply ordinary standard-tableau evacuation, which reverses this
descent set, and then use the same transposition, destandardization, and
semistandard Schützenberger--Lusztig involution as in the componentwise map.
Standard evacuation here is not the Weyl-group action on a semistandard
crystal; these operations already differ on standard tableaux of shape
((2,1)).  The resulting chromatic map and its inverse have exact target
coverage through rank five.  Transporting the ordinary Kashiwara operators
gives normal type-A crystal graphs on the colorings, with all lowering and
raising inverses checked through rank five.

## 3. The rank-five correction

For the Hessenberg code

\[
  (2,4,4,5,5),
\]

the only bad words are (34521) and (35241).  Their raw insertion tableau
is

\[
  \begin{array}{ccc}3&1&2\\5&4\end{array},
\]

with recording tableaux (125/34) and (135/24), respectively.  Replacing
the insertion tableau by

\[
  \begin{array}{ccc}2&1&3\\5&4\end{array}
\]

and leaving the recording tableau fixed fills the two missing targets.

The inverse correction must inspect the recording tableau.  The corrected
insertion tableau already occurs with the three recording tableaux
(123/45), (124/35), and (134/25).  Replacing it unconditionally would
therefore corrupt three valid fibers.  For the two exceptional recording
tableaux, we first restore the raw insertion tableau and then apply the
published inverse.

The same correction can be read as a last-cell rule.  The two four-letter
states have insertion tableau (21/54).  Inserting the final letter (3)
places it in the upper-right corner and puts the new recording label there.
Deletion removes these two entries and returns (3).  This description is
local for the two rank-five states, but it does not extend unchanged to rank
six.

## 4. The rank-six census

There are 132 natural unit interval orders on six naturally labelled
vertices.  Exhaustive insertion of all 720 permutations for every order gives
the following counts.

| property | count |
|---|---:|
| tested words | 95,040 |
| ladder-climbing orders | 12 |
| orders with a bad output | 12 |
| bad insertion tableaux | 112 |
| bad recording tableaux | 0 |
| collisions among raw pairs | 0 |

The bad column shapes are (102) occurrences of ((2,2,1,1)), seven of
((3,2,1)), and three of ((2,2,2)).  Comparing the bad outputs with the
missing targets in the same P-Knuth component and recording-descent fiber
gives a unique replacement in every case.  In 106 cases the replacement
keeps (Q).  The remaining six cases change both shape and (Q).

For example, take (P=(3,3,5,5,6,6)) and (w=463152).  The raw columns,
written from top to bottom, are

\[
  P_0=((4,6),(1,5),(3),(2)),
  \qquad
  Q_0=((1,2),(3,5),(4),(6)).
\]

The forced missing target is

\[
  P_1=((3,6),(1,5),(2,4)),
  \qquad
  Q_1=((1,2),(3,5),(4,6)).
\]

Thus the column shape changes from ((2,2,1,1)) to ((2,2,2)).  A rule
which keeps (Q), or which moves entries only until the (P)-tableau
conditions first hold, cannot produce this target.

The 112 replacements have ten cell actions, with multiplicities

\[
  54,14,12,7,6,6,4,4,3,2.
\]

They include swaps, three- and four-cell boundary rotations, simultaneous
top and bottom swaps, and six shape-changing rotations.  Each action is
stored as a pair of coordinate bijections, one for (P) and one for (Q),
so the action is independent of the numerical labels occupying the cells.

## 5. A reversible finite rule through rank six

For a bad rank-six output, record its column shape, the occupied cells in the
first two rows and first four columns, the pairwise (P)-comparison matrix of
the entries in these cells, and (operatorname{Des}(Q)).  Among the 112
defects, these data give 77 distinct source signatures, and each signature
selects one of the ten pair actions without conflict.

The corrected targets likewise give 77 target signatures with no conflicting
inverse actions.  A target is recognized as corrected by the following
reversible test.

1. Apply the inverse action selected by its target signature.
2. Check that the resulting insertion tableau is invalid.
3. Check that its source signature selects the forward inverse action.
4. Reapply the forward action and recover the given target.
5. Apply raw Kim--Pylyavskyy deletion and then raw insertion, and recover the
   candidate raw pair.

The first four conditions have two false positives among all rank-six
targets.  The raw deletion--insertion replay rejects both.  With all five
conditions, the inverse recognizes exactly the 112 corrected targets.  This
is an explicit bidirectional finite rewrite through rank six.  It does not
prove that translated rewrites are confluent in larger arrays, since the
present guard uses the global descent set of (Q).

## 6. Two obstructions to extrapolation

The chain interchange in Section 5 of paper-cache 354 is not a
Yang--Baxter map.  The first failures occur in rank six, including orders in
the Kim--Pylyavskyy avoidance class.  For (P=(1,2,4,5,6,6)), the two braid
orders applied to the chains (631,52,4) produce the words (164532) and
(641532).  These words lie in one P-Knuth component but their recording
descent sets force different insertion shapes.  Hence this interchange
cannot be used as a memoryless growth rule, and changing only (Q) cannot
repair its associator.

Kim--Pylyavskyy Example 7.11 gives the next representation obstruction.  For

\[
  P=(2,4,5,6,6,7,7),
  \qquad w=3156742,
\]

the raw (P)-columns are

\[
  ((1,3),(2,5,7),(6),(4)),
\]

and the raw (Q)-columns are

\[
  ((1,3),(2,4,7),(5),(6)).
\]

Their column heights are ((2,3,1,1)), so the raw output does not even have
partition shape.  An all-rank correction must therefore act on arbitrary
column arrays before converting them to tableaux.

The complete rank-seven raw census sharpens this example.  Across all 429
orders and all (5,040) permutations, the raw map has no pair collisions.
Exactly the 84 ladder-climbing orders have bad outputs.  There are 5,162 bad
insertion arrays and 142 bad recording arrays; the latter are exactly the
142 outputs of column-height composition ((2,3,1,1)).  The seven bad column
compositions and their multiplicities are

| column heights | multiplicity |
|---|---:|
| ((2,2,1,1,1)) | 3,543 |
| ((2,2,2,1)) | 833 |
| ((2,3,1,1)) | 142 |
| ((3,2,1,1)) | 546 |
| ((3,2,2)) | 14 |
| ((3,3,1)) | 68 |
| ((4,2,1)) | 16 |

The missing targets balance the bad outputs in every P-Knuth-component and
recording-descent fiber.  This produces a deterministic bijection after a
fixed finite ranking.  It is no longer a forced correction: 541 fibers have
more than one bad output, with maximum size five.  Even after fixing the
entire recording array and the first-column height, 352 matched subgroups
have size greater than one.  The resulting rank-seven ranking keeps (Q) in
4,702 cases; the remaining 460 cases change both shape and (Q).  It uses
133 insertion actions and 135 pair actions.  Thus the rank-seven extension is
a smaller global ranking problem inside the defect set, not a local rule
deduced from the present invariants.

Finally, Ehrhard's operators in paper-cache 349 are weak partial inverses.
They do not define normal type-A crystals.  Their alignments remain useful
as inspiration for possible guards, but they cannot supply the Kashiwara
axioms needed here.

## 7. Current boundary

The code now contains the exact forward column trace, the exact dualized
inverse, the rank-five insertion/deletion branch, the rank-six target oracle,
the 77 guarded forward and reverse signatures, and the rank-seven defect
ranking on arbitrary column arrays.  The next all-rank problem is to replace
the compiled actions and the residual rank-seven rankings by a boundary rule
with a decreasing measure and joinable overlaps.  Until such a rule is
proved, the componentwise map in `DIRECT_MAP.md` remains the all-rank
bijection and the local construction remains a verified finite prototype.
