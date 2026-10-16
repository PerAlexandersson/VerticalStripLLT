# Local Kim--Pylyavskyy insertion and its first corrections

This note records the exact Kim--Pylyavskyy column algorithm, its inverse,
and the finite corrections found through rank seven.  The primary source is
paper-cache 297, D.~Kim and P.~Pylyavskyy, *Robinson--Schensted correspondence
for unit interval orders*, arXiv:2003.12123v2.  We use Algorithms 1--3,
Proposition 5.6, Theorem 6.1, and Examples 7.9--7.11.

The result has three levels.

- On the avoidance class in Theorem 6.1, the published algorithm is a
  reversible insertion map.
- For all natural unit interval orders through rank six, a finite guarded
  correction gives a reversible bijection onto pairs of tableaux.
- In rank seven, a symmetric minimum-motion matching gives a reversible
  bijection without an arbitrary ordering of the defects.  This matching is
  fiber-global and does not yet give an all-rank insertion rule.

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
recording-descent fiber.  There are 541 fibers with more than one bad output,
and the maximum size is five.  Even after fixing the entire recording array
and the first-column height, 352 matched subgroups have size greater than
one.  A lexicographic ranking gives a bijection, but the ranking is not needed:
the symmetric matching in the next section determines all these assignments.

Finally, Ehrhard's operators in paper-cache 349 are weak partial inverses.
They do not define normal type-A crystals.  Their alignments remain useful
as inspiration for possible guards, but they cannot supply the Kashiwara
axioms needed here.

## 7. A choice-free matching in rank seven

We compare a bad pair ((P_0,Q_0)) with a missing target ((P_1,Q_1)) by the
entries which change cells.  Let (m_P) and (m_Q) be the numbers of moved
entries in the two arrays, and let (d_P) and (d_Q) be the corresponding total
Manhattan distances.  The cost of the pair is

\[
  (m_P+m_Q,d_P+d_Q,m_Q,d_Q).
\]

Inside a fixed recording-array and first-column-height group, we first match
as many sources and targets as possible.  Among these maximum-cardinality
matchings, we minimize the sum of the four cost coordinates.  If two
matchings have the same total, we sort their lists of pair costs in decreasing
order and minimize these lists lexicographically.  This last comparison
minimizes the worst individual repair after minimizing the total repair.

This rule is symmetric in source and target.  Exhaustively, it has a unique
optimum in all 352 nontrivial groups in rank seven.  The total cost alone is
unique in 320 groups and has ties in 32 groups, with at most three optimal
matchings.  The decreasing cost list resolves every tie.  This also handles
the nine groups in which the source and target cardinalities differ: their
unmatched elements pass to the next stage.

We next group the unmatched elements by first-column height and apply the same
maximum-cardinality minimum-motion rule.  Both nontrivial height groups have a
unique optimum.  Every final residual fiber has size at most one.  Hence the
construction has no lexicographic or other ordering choice through rank seven.
It keeps (Q) in 4,702 of the 5,162 repairs; 460 repairs change both shape and
(Q).  The minimum-motion assignment uses 73 insertion actions, equal to the
number of pair actions.

The first ambiguous exact-recording group illustrates the change.  For
(P=(2,3,5,5,6,7,7)), the old lexicographic pairing moves fourteen entries,
whereas the unique minimum-motion pairing moves six.  Thus much of the larger
lexicographic action catalogue came from the ordering rather than the
Kim--Pylyavskyy defect.

The matching requires the complete sets of bad outputs and missing targets in
a component and recording-descent fiber.  Its uniqueness therefore gives a
reversible finite bijection, but not a local insertion recurrence.

## 8. Bidirectional boundary guards through rank seven

The minimum-motion actions admit a finite boundary description.  Every raw
Kim--Pylyavskyy column is a (P)-chain, so a bad array has either a shape
violation (h_j<h_{j+1}) or a row violation

\[
  P(r,j+1)<_P P(r,j).
\]

We choose the leftmost boundary (j), and then the topmost violating row (r).
For a shape violation we put (r=h_j).  In the rank-seven census, the only
boundaries are

| type and position | multiplicity |
|---|---:|
| row, ((j,r)=(0,0)) | 3,742 |
| row, ((j,r)=(0,1)) | 987 |
| row, ((j,r)=(1,0)) | 355 |
| shape, ((j,r)=(0,2)) | 78 |

The forward guard records the occupied cells and all pairwise (P)-comparisons
in the window

\[
  r-1\leq \text{row}\leq r+1,
  \qquad
  j-1\leq \text{column}\leq j+4,
\]

together with the complete recording columns (j) and (j+1).  The window is
clipped at the edge of the array.  These data give 2,532 signatures and select
one of the 73 pair actions without conflict on all 5,162 defects.  After
translating cells and moves relative to ((j,r)), neither the global shape nor
the absolute position is needed.  Every observed action is supported between
columns (j-1) and (j+4).

The recording labels cannot be replaced by their relative order: doing so
leaves 132 conflicting signatures.  For example, for
(P=(3,3,5,5,6,6,7)), the words (4376512) and (4573612) have the same raw
insertion array

\[
  ((4,6,7),(1,5),(3),(2))
\]

and the same recording descent set ({2,4}).  The recording arrays
(((1,3,5),(2,4),(6),(7))) and
(((1,3,5),(2,6),(4),(7))) select different repairs.  Thus the raw insertion
array and the recording descent set do not determine the forward action.

For the inverse, the pairwise (P)-comparisons in the first three rows and
first five columns, together with the complete recording array, give 2,693
signatures.  They have no action conflicts and occur on exactly the 5,162
corrected targets among all 2,162,160 rank-seven targets.  A more local inverse
tries the boundary positions above, using five rows and the same six-column
window together with the two adjacent recording columns.  This gives 5,850
candidates.  The forward guard rejects 140 candidates, and dual
Kim--Pylyavskyy deletion followed by reinsertion rejects a further 548.
Exactly the 5,162 corrected targets remain, each with a unique inverse action.

Of the 73 pair actions, 62 preserve the column shape and 11 change it.  The
numbers moving (2,3,4,5,6) insertion entries are respectively
(13,13,26,17,4).  There are 66 pair motions after translating the boundary to
the origin, and 59 insertion motions up to arbitrary translation.

One branch already has a uniform description.  Suppose the first defect is
the shape boundary between columns of heights (2) and (3), followed by two
columns of height (1).  Write the latter three insertion columns from top to
bottom as

\[
  (a,b,c),\qquad (d),\qquad (e).
\]

Replace them by

\[
  (e,c),\qquad (a,d),\qquad (b),
\]

and move the bottom recording entry of the height-three column to the bottom
of the next recording column.  This rule agrees with the minimum-motion map
in all 78 cases whose first defect is a shape defect.  The other 64 malformed
arrays have an earlier row defect and belong to the row branch.

A second uniform branch covers every transposition action.  At a row defect
((j,r)), swap the offending left cell with one of the five relative positions

\[
  (j+2,r),\quad (j+3,r),\quad (j+4,r),\quad
  (j+2,r-1),\quad (j+2,r+1),
\]

and leave (Q) fixed.  Restrict the raw and candidate column-reading words to
the interval containing the two changed positions, enlarged by one unchanged
letter at each end, and require a P-Knuth path between these short words.
Also require a valid (P)-tableau and exclude pairs already in the raw image by
Kim--Pylyavskyy deletion--reinsertion.  Minimum displacement then selects one
target on exactly 2,779 sources, always the assigned target, and selects no
target on the other 2,383 defects.  There are no ties.  The local certificates
have length five, six, or seven and require at most 16 elementary P-Knuth
moves.  Thus this removes thirteen of the 73 actions from the table without a
whole-component oracle.

A source-by-source nearest repair cannot describe the row branch.  In the
staged matching, 5,076 sources receive their unique individual minimum, three
have a tied minimum, and 83 receive a strictly more expensive target in order
to make the assignment bijective.  Even if we restrict to the 66 observed
local motions, require the same P-Knuth component, and exclude targets in the
raw image by deletion--reinsertion, 35 assigned targets are not individually
minimal.  The first example is the two-source fiber for
(P=(2,4,5,6,7,7,7)) described above: both sources prefer the same target, so
the decreasing pair-cost profile assigns the other target to one source.

This gives a bidirectional finite rule through rank seven which no longer uses
the missing-target set when it is applied.  Its remaining action table was
obtained from the minimum-motion matching; an all-rank rule still requires a
uniform description of the cycle and path actions and a proof that
overlapping repairs are joinable.

## 9. Current boundary

The code now contains the exact forward column trace, the exact dualized
inverse, the rank-five insertion/deletion branch, the rank-six target oracle,
the 77 guarded forward and reverse signatures, and the rank-seven
minimum-motion matching and boundary guards on arbitrary column arrays.  The
next all-rank problem is to replace the 73-entry action table by uniform cases
and prove that their translated overlaps terminate and are joinable.  Until
such a rule is proved, the componentwise map in `DIRECT_MAP.md` remains the
all-rank bijection and the local construction remains a verified finite
prototype.
