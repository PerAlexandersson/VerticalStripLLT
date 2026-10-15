# Chromatic generalized RSK: signed sets and involutions

This note specifies the finite objects and local involutions used by the
chromatic Garsia--Milne bijection.  It
uses the conventions of Shareshian--Wachs, arXiv:1405.4629v2, Section 6.
The Kim--Pylyavskyy tableaux are conjugated relative to these tableaux, so we
do not mix the two conventions below.

The source audit used the cached full texts, not abstracts or secondary
summaries:

- paper-cache 350, Shareshian--Wachs, arXiv:1405.4629v2: Section 4 for the
  odd-component color switch and Section 6, especially Theorem 6.3 and its
  proof, for the array involution;
- paper-cache 349, Ehrhard, arXiv:2205.01834v1: Sections 3--6 for the weak
  crystal definition, alignment, operators, and componentwise
  Jacobi--Trudi cancellation;
- paper-cache 297, Kim--Pylyavskyy, arXiv:2003.12123: Algorithm 1, Theorem
  6.1, and its proof in Section 9 for the avoidance-class oracle.

The inverse-Kostka direction was also checked against Eğecioğlu--Remmel's
1990 inverse-Kostka paper and the full official arXiv text of
Allen--Celano--Mason, arXiv:2511.18156.  The implementation follows their
Theorem 2.4 and Algorithms 4.2, 5.1, and 5.4.

## 1. Posets, arrays, and the two statistics

Let (P=P(m_1,\dotsc,m_{n-1})) be a natural unit interval order on
([n]), where

\[
  i <_P j \quad\Longleftrightarrow\quad i<j\text{ and }j>m_i.
\]

Its incomparability graph (G) has an edge (\{i,j\}), for (i<j),
exactly when (j\leq m_i).  A proper coloring
(\kappa:[n]\to[k]) is identified with the (P)-array whose row (r)
is the increasing (P)-chain (\kappa^{-1}(r)).  Its weight is the weak
composition

\[
  \operatorname{wt}(\kappa)
  =(|\kappa^{-1}(1)|,\dotsc,|\kappa^{-1}(k)|).
\]

We use

\[
\begin{split}
  \operatorname{asc}(\kappa)
  &=\#\{\{i,j\}\in E(G):i<j,\ \kappa(i)<\kappa(j)\},\\
  \operatorname{des}(\kappa)
  &=\#\{\{i,j\}\in E(G):i<j,\ \kappa(i)>\kappa(j)\}.
\end{split}
\]

Every edge has differently colored endpoints, so their sum is
(|E(G)|).  For a (P)-array (A), the statistic called
(\operatorname{inv}_G(A)) by Shareshian--Wachs is
(\operatorname{des}(\kappa_A)).

A Shareshian--Wachs (P)-tableau is a (P)-array of partition shape
(\lambda) such that an entry below another entry in the same column is
not smaller in (P).  For such a tableau (T),
(\operatorname{inv}_G(T)) counts edges (\{i,j\}), with (i<j), for
which (i) is in a lower row than (j).

## 2. The Shareshian--Wachs signed set

Pad (\lambda\vdash n) to length (n).  For (\pi\in S_n), put

\[
  \alpha(\lambda,\pi)_i
  =\lambda_{\pi(i)}-\pi(i)+i.
\]

Terms with a negative part are empty.  Define the signed set

\[
  \mathcal X_\lambda
  =\bigsqcup_{\pi\in S_n}
    \{\pi\}\times\mathcal A_{\alpha(\lambda,\pi)},
  \qquad
  \operatorname{sgn}(\pi,A)=\operatorname{sgn}(\pi),
\]

where (\mathcal A_\alpha) is the set of (P)-arrays of shape
(\alpha).  Give every element the (q)-degree
(\operatorname{inv}_G(A)=\operatorname{des}(\kappa_A)).

For a non-tableau array, call (A_{i,c}) bad when (i>1), the cell is
occupied, and the cell above it is either absent or greater in (P).
Choose the smallest bad column (c), and then the largest (r) for
which (A_{r+1,c}) is bad.  In row (r), retain the entries before
column (c); in row (r+1), retain the entries through column (c).
On the remaining suffixes, beginning at column (c) in row (r) and
at column (c+1) in row (r+1), take the induced subgraph of (G).
Swap the two rows on every odd connected component and leave every
even component unchanged.  Finally replace (\pi) by
(\pi(r,r+1)).

This is the sign-reversing involution in the proof of
Shareshian--Wachs Theorem 6.3.  It preserves
(\operatorname{inv}_G(A)).  Its positive fixed points are precisely
the (P)-tableaux of shape (\lambda), with (\pi=\mathrm{id}).

## 3. Weight normalization

For adjacent colors (r,r+1), the Shareshian--Wachs involution
(\psi_r) swaps the colors on every odd connected component of the
subgraph induced by these two colors.  It interchanges the two entries
of the weight composition and preserves both ascent and descent number.

For a weak composition (\alpha), choose the stable bubble-sort word
(b(\alpha)=(r_1,\dotsc,r_s)) which rearranges (\alpha) into the
weakly decreasing partition (\alpha^+).  Then

\[
  \Theta_\alpha
  =\psi_{r_s}\dotsm\psi_{r_1}:
  \mathcal A_\alpha\longrightarrow\mathcal A_{\alpha^+}
\]

is a statistic-preserving bijection.  Its inverse applies the same
adjacent swaps in reverse order.  This normalization lets us use
partition-indexed Kostka matrices while retaining an explicit trace.

## 4. Jacobi--Trudi coefficients and inverse Kostka indexing

For partitions (\lambda,\nu\vdash n), define

\[
  \mathcal J_{\lambda,\nu}
  =\{\pi\in S_n:
      \alpha(\lambda,\pi)_i\geq0\text{ for all }i,
      \ \alpha(\lambda,\pi)^+=\nu\},
\]

with sign (\operatorname{sgn}(\pi)).  Its signed cardinality is the
coefficient of (h_\nu) in (s_\lambda).  If
(K_{\lambda,\mu}) denotes the number of ordinary semistandard Young
tableaux of shape (\lambda) and content (\mu), then

\[
  \sum_{\lambda\vdash n}
  K_{\lambda,\mu}
  \sum_{\pi\in\mathcal J_{\lambda,\nu}}
  \operatorname{sgn}(\pi)
  =\delta_{\mu,\nu}.
\]

With the conventional row-shape, column-content indexing of (K),
this is the transpose of (K^{-1}K=I).  It is the historically harder
order of the inverse-Kostka identity.  Eğecioğlu--Remmel gave an
involution for (KK^{-1}=I) and explicitly left (K^{-1}K=I) open.
Loehr--Mendes gave the first full proof of the reverse identity in 2006.
Allen--Celano--Mason, arXiv:2511.18156, subsequently gave an independent
construction using the Garsia--Milne involution principle.

Allen--Celano--Mason's Theorem 2.4 gives the exact change of variables
needed here.  Set (\sigma=\pi^{-1}) and
(\Delta_j=\lambda_j-j+\sigma(j)).  Then
(\Delta_{\pi(i)}=\alpha(\lambda,\pi)_i), and the two permutations have
the same sign.  A nonnegative determinant term fixes every zero-padding
position, so trailing zeros can be stripped.  Their Algorithm 5.4 on a
special rim-hook tabloid and a semistandard tableau therefore transfers to
our triples ((\lambda,\pi,Q)) while preserving (\nu).  The tabloid is
reconstructible from (\sigma), so it need not be stored as extra certificate
state.

Equivalently, if

\[
  D_{\lambda,\nu}
  =\sum_{\pi\in\mathcal J_{\lambda,\nu}}\operatorname{sgn}(\pi),
\]

then (D_{\lambda,\nu}=(K^{-1})_{\nu,\lambda}) and the required
entrywise identity is

\[
  \sum_\lambda D_{\lambda,\nu}K_{\lambda,\mu}
  =(K^{-1}K)_{\nu,\mu}.
\]

This form removes any ambiguity about which matrix order the cancellation
must realize.

Consequently, the ordinary LGV tail switch proving Jacobi--Trudi is not
by itself the second involution needed below.  We use
Allen--Celano--Mason Algorithm 5.4 on

\[
  \bigsqcup_{\lambda\vdash n}
  \mathcal J_{\lambda,\nu}
  \times\operatorname{SSYT}(\lambda,\mu).
\]

For composition content (\mu), first use ordinary Bender--Knuth
involutions to change the tableau content to (\mu^+).  Replace (\pi) by
(\sigma=\pi^{-1}) and regard ((\lambda,\sigma,Q)) as the tunnel-hook
covering and semistandard tableau used in their construction.  Algorithm
4.2 moves one entry between rows of the corresponding immaculate tableau,
possibly inserting or deleting a row.  When the result is not
semistandard, Algorithm 5.1 applies its bad-cell tail switch.  Alternating
these two local involutions reaches the other semistandard endpoint.
Finally invert (\sigma) and undo the ordinary Bender--Knuth maps.  When
(\nu=\mu^+), the unique positive state is fixed.

## 5. The common signed set

Fix a weak weight (\mu=(\mu_1,\dotsc,\mu_k)) of total size (n), and write
(\bar\mu=\mu^+) for its decreasing rearrangement with zero parts removed.
The Bender--Knuth maps identify its Kostka number with that of
(\bar\mu).  The common signed set is

\[
  \mathcal S_\mu
  =\bigsqcup_{\nu,\lambda\vdash n}
  \mathcal A_\nu
  \times\mathcal J_{\lambda,\nu}
  \times\operatorname{SSYT}(\lambda,\mu).
\]

The sign is the sign of (\pi\in\mathcal J_{\lambda,\nu}), and the
(q)-degree is (\operatorname{des}(A)).

There are two sign-reversing involutions on this same finite set.

1. For fixed (A\in\mathcal A_\nu), apply the reverse
   inverse-Kostka involution to
   ((\lambda,\pi,Q)).  Its fixed set is empty when
   (\nu\neq\bar\mu) and consists of one positive state when
   (\nu=\bar\mu).  The tableaux retain their original content (\mu);
   only their cardinality depends on the rearrangement.  Thus its fixed
   points are identified with (\mathcal A_{\bar\mu}).
2. Convert (A) to shape (\alpha(\lambda,\pi)) using
   (\Theta^{-1}_{\alpha(\lambda,\pi)}), apply the
   Shareshian--Wachs involution, and normalize the resulting array
   again.  Leave (Q) unchanged.  Its fixed points are the pairs
   ((T,Q)) in which (T) is a (P)-tableau and (Q) is an ordinary
   semistandard tableau of the same shape and content (\mu).

Starting at a fixed point of the first involution and alternating the
two involutions until reaching a fixed point of the second is the
Garsia--Milne map.  Every step is reversible.  A trace records the signed
states, the selected Shareshian--Wachs bad cell, the local Algorithm 4.2
row move or Algorithm 5.1 bad cell, and the adjacent-swap words used by the
normalizations.

## 6. Converting ascent to the array inversion statistic

The array involution preserves descent number, while the requested map
starts with ascent number.  For a coloring in the fixed alphabet ([k]) of weight
(\mu=(\mu_1,\dotsc,\mu_k)), complement the colors by
(r\mapsto k+1-r).  This changes the weight to
((\mu_k,\dotsc,\mu_1)) and changes ascent number into descent number.
Apply a fixed adjacent-swap word, using the maps (\psi_r), which
rearranges the reversed weight back to (\mu).  The resulting bijection

\[
  R_\mu:\mathcal A_\mu\longrightarrow\mathcal A_\mu
\]

satisfies

\[
  \operatorname{des}(R_\mu(A))=\operatorname{asc}(A).
\]

After (R_\mu), apply the normalization
(\Theta_\mu:\mathcal A_\mu\to\mathcal A_{\bar\mu}) and then the
Garsia--Milne map.  This gives the requested statistic orientation without
changing the final tableau content.  The inverse map first runs the
alternating trace backwards, then applies (\Theta_\mu^{-1}) and
(R_\mu^{-1}).

## 7. Ehrhard and Kim--Pylyavskyy

Ehrhard's Definition 3 uses the word *crystal* for a colored graph in
which (e_r) and (f_r) are partial inverses and shift the weight by a
simple root.  The paper does not prove normality, the type-A local
axioms, or that a connected component is a highest-weight crystal
(B(\lambda)).  Its Section 6 instead proves Schur positivity of each
component by another Jacobi--Trudi sign-reversing involution, and its
Figure 8 has a connected component with two highest-weight elements.
Thus these are weak partial-inverse operators, not the classical
Kashiwara operators required here.  The alignment is useful as a model
for local reversible bookkeeping, but it cannot be used as the desired
crystal structure.

Kim--Pylyavskyy construct a bijection

\[
  S_n\longleftrightarrow
  \bigsqcup_{\lambda\vdash n}
  \operatorname{P\text{-}Tab}(\lambda)
  \times\operatorname{SYT}(\lambda)
\]

when (P) avoids (P_{(3,1,1),5}) and (P_{(4,2,1,1),6}).
Their tableaux are conjugated relative to the Shareshian--Wachs
convention.  Theorem 6.1 preserves the relevant descent data, and
P-Knuth equivalence preserves the fake (P)-inversion statistic.

Their map extends to a repeated-color oracle as follows.  Write every color
class as a decreasing (P)-chain and concatenate the blocks in increasing
color order to obtain a permutation (w).  Internal block positions are
(P)-descents.  If (P\text{-}RS(w)=(U,V)), put
(T=U^{\mathsf t}) in the Shareshian--Wachs convention and
(W=(\operatorname{evac}V)^{\mathsf t}).  Theorem 6.1(B) gives

\[
  \operatorname{Des}(W)=[n-1]\setminus\operatorname{Des}_P(w),
\]

so every descent of (W) is a block boundary and (W) uniquely
destandardizes to an ordinary semistandard tableau (Q) of content (\mu).
The inverse standardizes (Q), transposes and evacuates, applies inverse
(P)-RS, and checks that the recovered blocks are decreasing (P)-chains.
Moreover the fake inversion statistic of (w) equals
(\operatorname{des}(\kappa)=\operatorname{inv}_G(T)).  This is a genuine
repeated-color weight/descent correspondence on the avoidance class;
precomposition by (R_\mu) gives the requested ascent orientation.  It is
an oracle rather than a general solution because Kim--Pylyavskyy's pattern
avoidance hypothesis is essential.

## 8. The bijection and transported crystal

Let (\Phi_{P,k}) be the following composition on proper colorings
(\kappa:[n]\to[k]).

1. Apply (R_\mu) to replace ascent number by descent number.
2. Apply (\Theta_\mu) and attach the unique positive fixed state of the
   reverse inverse-Kostka involution.
3. Alternate the conjugated Shareshian--Wachs involution and the local
   Allen--Celano--Mason involution until the former is fixed.

The inverse starts at ((T,Q)), alternates the same involutions in the opposite
order, and then applies (\Theta_\mu^{-1}) and (R_\mu^{-1}).  The involution
principle therefore gives a bijection

\[
  \Phi_{P,k}:\{\text{proper colorings }[n]\to[k]\}
  \longrightarrow
  \bigsqcup_{\lambda\vdash n}
  \operatorname{PTab}_P(\lambda)
  \times\operatorname{SSYT}_k(\lambda)
\]

such that

\[
  \operatorname{wt}(Q)=\operatorname{wt}(\kappa),\qquad
  \operatorname{asc}(\kappa)=\operatorname{inv}_G(T).
\]

Zero parts of (\mu) cause no difficulty: both kinds of Bender--Knuth maps
allow empty adjacent color classes.  Hence the source and target are stable
under the ordinary type-A Kashiwara operators.  Read (Q) from the bottom row
to the top row and from left to right within each row.  For the letters
(i,i+1), cancel pairs ((i+1)i).  Then (e_i) changes the first unmatched
(i+1) into (i), while (f_i) changes the last unmatched (i) into (i+1).
Define

\[
  e_i^P=\Phi_{P,k}^{-1}e_i\Phi_{P,k},\qquad
  f_i^P=\Phi_{P,k}^{-1}f_i\Phi_{P,k}.
\]

These are genuine normal type-A crystal operators.  They preserve
(\operatorname{asc}) because they change (Q) while leaving (T) fixed.
More precisely, there is an isomorphism of colored directed graphs

\[
  \operatorname{Col}_k(P)
  \cong
  \bigsqcup_{\lambda\vdash n}
  \bigsqcup_{T\in\operatorname{PTab}_P(\lambda)} B_k(\lambda).
\]

Thus each component is indexed by one (P)-tableau (T), has a unique
highest-weight coloring, and is an ordinary highest-weight crystal of shape
(\lambda).  If (\varepsilon_i) and (\varphi_i) are the two string lengths,
then

\[
  \varphi_i(\kappa)-\varepsilon_i(\kappa)
  =\operatorname{wt}_i(\kappa)-\operatorname{wt}_{i+1}(\kappa).
\]

The value of (\operatorname{asc}) is constant on this component and equals
(\operatorname{inv}_G(T)).  In particular, the fixed-ascent character is a
sum of Schur characters, one for each (P)-tableau with the corresponding
inversion number.

The total crystal reflection is an especially useful invariant.  Put
(d_i(\kappa)=\operatorname{wt}_i(\kappa)-
\operatorname{wt}_{i+1}(\kappa)) and define

\[
  S_i^P(\kappa)=
  \begin{cases}
    (f_i^P)^{d_i(\kappa)}\kappa,&d_i(\kappa)\geq0,\\
    (e_i^P)^{-d_i(\kappa)}\kappa,&d_i(\kappa)<0.
  \end{cases}
\]

Equivalently, (S_i^P=\Phi_{P,k}^{-1}S_i\Phi_{P,k}), where (S_i) reverses
the (i)-string of (Q).  These maps are total involutions, preserve ascent,
interchange the two relevant weight entries, and satisfy

\[
  (S_i^P)^2=1,\qquad
  S_i^PS_j^P=S_j^PS_i^P\quad(|i-j|>1),\qquad
  S_i^PS_{i+1}^PS_i^P=S_{i+1}^PS_i^PS_{i+1}^P.
\]

This crystal reflection must not be conflated with the classical
Bender--Knuth involution on semistandard tableaux.  The latter swaps content
but does not in general satisfy the braid relation.  Nor is (S_i^P) the
Shareshian--Wachs odd-component switch (\psi_i).  For the two-element chain,
(S_1^P(12)=12) whereas (\psi_1(12)=21).  Exhaustively through rank five,
169,220 of 226,008 transported reflections agree with (\psi_i), while
(\psi_i) fails 7,236 of 169,016 adjacent braid tests.

Let (R_i) denote the increasing-order component-signature reflection obtained
from Ehrhard's alignment, and use right-to-left composition.  The correction

\[
  C_i=S_i^P R_i
\]

preserves weight and ascent.  It is the post-correction in
(S_i^P\kappa=C_i(R_i\kappa)); equivalently,
(S_i^P=R_iC_i^{-1}).  Since both factors are involutions,

\[
  C_i^{-1}=R_iS_i^P,
  \qquad
  R_iC_iR_i=S_i^PC_iS_i^P=C_i^{-1}.
\]

The correction is not itself an involution.  Even for the three-element
chain, on words with two (1)'s and one (2), it has the cycle

\[
  112\longmapsto121\longmapsto211\longmapsto112,
\]

and it similarly cycles (122,212,221).  Thus (C_i) measures both the gauge
chosen by the signed bijection (which does not specialize to ordinary RSK on
a chain) and the genuine failure of the weak component reflections to satisfy
rank-two compatibility.

There is an exact rank-two bookkeeping identity.  For adjacent (i,j), put

\[
  D_{ij}=(R_iR_j)^3,
\]

and write ({}^gH=gHg^{-1}).  If

\[
\begin{split}
  L_{ij}&=C_i({}^{R_i}C_j)({}^{R_iR_j}C_i),\\
  M_{ij}&=C_j({}^{R_j}C_i)({}^{R_jR_i}C_j),
\end{split}
\]

then the braid relation for the transported reflections is precisely

\[
  L_{ij}D_{ij}=M_{ij},
  \qquad\text{or equivalently}\qquad
  D_{ij}=L_{ij}^{-1}M_{ij}.
\]

Thus (D_{ij}) is the weak reflection's rank-two holonomy and the correction
cocycle cancels it.  On the first rank-six obstruction above, (D_{12}) has
the three-cycle

\[
  233231\longmapsto133232\longmapsto233213\longmapsto233231
\]

and fixes the other 19 proper colorings of weight ((1,2,3)).  Among these 22
colorings, 11 have ascent one and 11 have ascent two; the moved three-cycle
has ascent one.  The full (R_1,R_2)-orbit is an 18-cycle of ascent one
containing three colorings over each of the six permutations of ((3,2,1)).
It is therefore a three-sheeted cover of the Coxeter hexagon rather than a
genuine symmetric group orbit.

In particular, there is no single global relabeling (H) with
(S_i^P=HR_iH^{-1}) for every (i): simultaneous conjugation would preserve the
failed braid relation.  Any remedy must therefore be root-dependent, as the
cocycle (C_i) is, or enrich the state by sheet data.

Even the complete ordered component words for both simple roots do not
determine the sheet.  For the same order, the colorings (132121) and (312121)
have weight ((3,2,1)), ascent one, and identical ordered colored component
words

\[
  1\mid2121 \quad\text{for }(1,2),
  \qquad
  3\mid2\mid2 \quad\text{for }(2,3).
\]

Nevertheless,

\[
  D_{12}(132121)=123121,
  \qquad
  D_{12}(312121)=312121.
\]

The two colorings differ only by interchanging colors (1) and (3) on the two
isolated initial vertices.  Hence the separate component lists lose essential
cross-root interleaving information; any intrinsic rule needs vertex labels or
an equivalent compatibility datum linking the two root decompositions.

The sheet number is not uniformly three.  Across every rank-six order and all
1,296 proper colorings of content ((3,2,1)), the cycle inventory of (D_{12})
is 1,258 fixed points, eleven 3-cycles, and one 5-cycle.  The 5-cycle occurs
for the connected path, with Hessenberg code ((2,3,4,5,6,6)):

\[
  121321\mapsto132121\mapsto212131\mapsto312121
  \mapsto213121\mapsto121321.
\]

Its weak rank-two orbit is a 30-cycle, hence a five-sheeted cover of the
Coxeter hexagon.  Thus no universal (\mathbb Z/3\mathbb Z)-valued sheet charge
can repair the weak action.

Through rank five, (C_i) fixes 197,212 of 226,008 state/root pairs.  Its
nontrivial cycles have lengths from 2 through 20, with gaps, and it can change
both insertion shape and insertion tableau.  Inverse-Kostka traversal is
strongly correlated with nontrivial correction but is not necessary: 3,260
nontrivial corrections occur when none of the source, its (R_i)-image, or its
(C_i)-image uses an inverse-Kostka edge.  The first is the displayed chain
cycle.  Hence inverse Kostka is a bottleneck, but not the sole source of the
nonlocal gauge.

The four observed presence/absence masks are not an additional empirical
phenomenon.  A forward Garsia--Milne path uses an inverse-Kostka edge exactly
when its terminal shape differs from the decreasing rearrangement of its
content.  One implication is immediate from the canonical initial triple.
For the converse, a terminal fixed point with canonical shape has canonical
(nu), hence is fixed by the inverse-Kostka involution; being fixed by both
alternating involutions makes its path isolated.  Since (R_i) and (C_i)
preserve sorted content and (T(C_i\kappa)=T(R_i\kappa)), the latter two
endpoints necessarily have the same inverse-Kostka presence bit.

There is nevertheless an exact component statement:

\[
  T(C_i\kappa)=T(R_i\kappa).
\]

Indeed, (C_i\kappa=S_i^P(R_i\kappa)) and the transported crystal reflection
preserves the insertion tableau.  Hence (C_i) compares the original coloring
with a point in the weakly reflected insertion component; its remaining
motion inside that component is the signed-bijection gauge.

There is, however, an exact reversible trace certificate.  Flatten the local
inverse-Kostka events into a single ordered (psi/theta) word.  A (psi) letter
retains its source and target rows and its row-insertion/deletion flags; a
(theta) letter retains its row and column.  We discard the intermediate
partitions, the inverse-Kostka edge boundaries, and all Shareshian--Wachs
events.  Then, for each fixed order, the triple

\[
  (\operatorname{wt}(\kappa),T(\kappa),
    \text{detailed inverse-Kostka word of }\kappa)
\]

determines (\kappa).  Indeed, start with the row-constant normalized tableau
of shape (\operatorname{sort}(\operatorname{wt}(\kappa))).  Replay each
recorded row move or tail switch, then undo the fixed content normalization.
This reconstructs the final ((\lambda,Q)); intervening Shareshian--Wachs moves
change only the permutation coordinate and therefore do not affect the replay.
Together with (T), the inverse bijection recovers (\kappa).

The implementation asserts this replay identity on all 56,993 full-alphabet
proper colorings through rank five.  Among the 28,796 nontrivial correction
states, 5,780 preserve the detailed word (2,520 with a nonempty word), but none
preserve both (T) and the word.  The certificate is therefore reversible, but
an intrinsic rule for updating it under (S_i^P) remains to be found.

The component anchor does have a direct description.  For the highest tableau
(Q_\lambda^{\mathrm{high}}), the reverse inverse-Kostka involution is already
fixed and no alternating path is traversed.  Consequently the highest-weight
coloring in the component indexed by (T) is

\[
  \kappa_T^{\mathrm{high}}=R_\lambda^{-1}(T),
\]

where (T) is regarded as its row coloring and (R_\lambda) is the
ascent-to-descent orientation map from Section 6.  This identity was checked
for every component through rank five.

This transport does not make the operators local on the coloring.  Already
for the chain on three elements, the constructed map gives
(f_1(112)=221); all three positions change.  With three colors it gives
(f_1(132)=322), so even a color outside the active pair can move.  The
chain on four elements gives a stronger obstruction.  The colorings (1134)
and (1143) have the same weight ((2,0,1,1)), the same ascent number, and the
same labeled restriction to colors (1,2), but

\[
  f_1(1134)=2134,
  \qquad
  f_1(1143)=4321.
\]

Consequently no rule depending only on the induced two-color subgraph can
describe these transported operators.  A possible intrinsic description must
retain global word, growth-diagram, or signed-trace information.  This is a
property of the present explicit bijection, not a claim that every possible
chromatic RSK bijection has nonlocal crystal operators.

The reflections are somewhat less nonlocal than the individual Kashiwara
edges, but they are still global.  On the four-element chain, in one-based
colors,

\[
  S_2^P(1223)=2331,
\]

so a color outside the active pair moves.  A natural attempt is to order the
odd components of the two-color induced graph, cancel their majority-color
signs, and flip only the excess unmatched components.  All four basic choices
of increasing/decreasing order and cancellation orientation satisfy braid
through rank five, but this range is structurally vacuous.  The first
constraining content is ((3,2,1)) at rank six, where every choice fails.  For
the increasing-order, (i(i+1))-cancellation convention, the first failure has
Hessenberg code ((1,2,4,5,6,6)) and coloring (121321):

\[
  S_1S_2S_1(121321)=133232,
  \qquad
  S_2S_1S_2(121321)=233231.
\]

Thus the obvious signature pairing of odd components does not provide a Weyl
group action, despite every rank-five test passing.  An independent
implementation of Ehrhard's alignment and weak operators agrees with this
signature reflection on all 2,592 single-reflection checks in the rank-six
((3,2,1)) orbit.  The braid failure therefore also gives an exact small
certificate that Ehrhard's operators are not a normal type-A crystal.

Nor does ordinary standardization compress the global information.  Increasing
tie order fails on the two-element chain and the constant coloring, while
decreasing tie order first fails on the three-element chain: standardizing
(111) to (321) changes the insertion shape from ((3)) to ((2,1)).  Hence this
(\Phi_{P,k}) is not the destandardization of its restriction to permutation
colorings.

There is nevertheless a useful compression of the obstruction.  On the union
of common signed sets over all contents, let (F_i) act only on (Q).  If (J)
is the conjugated Shareshian--Wachs involution, then

\[
  JF_i=F_iJ
\]

with equality of definedness, since (J) leaves (Q) unchanged and its decision
uses only ((A,\lambda,\pi)).  The failure is concentrated in the source
normalization and the reverse-inverse-Kostka involution (I).  Already for
(n=2), (\nu=(2)), (\mu=(1,1)), and
(u=((2),\mathrm{id},[1\ 2])), the expression (F_1I(u)) is undefined, whereas
(IF_1(u))=F_1(u) is the diagonal state with recording row ([2\ 2]).  This
suggests carrying the marked unmatched cell freely across (J)-events and
expanding the trace only at the critical Allen--Celano--Mason events where
(F_i) and (I) do not commute.

The Rust implementation exhausts all natural unit interval orders with
(n\leq5), all packed source fibers, every reverse inverse-Kostka endpoint,
and every placement of one empty color class.  It also checks both transported
operators wherever they are defined.  The exact counts and the two minimal
failed LGV variants are recorded in `COMPUTATION.md`.
