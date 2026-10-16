# A direct chromatic P-array RSK map

This note gives an explicit bijection from proper colorings of a natural unit
interval order to pairs consisting of a Shareshian--Wachs P-tableau and an
ordinary semistandard tableau. It uses P-Knuth components rather than the
signed inverse-Kostka construction. The map is deterministic and valid for
every natural unit interval order, although its present definition enumerates
an entire P-Knuth component.

The primary source is paper-cache 354, J.~Blasiak, H.~Eriksson,
P.~Pylyavskyy, and I.~Siegl, *Noncommutative Schur functions for posets*,
arXiv:2211.03967v2. We use Definitions 2.3, 3.2, and 3.7, Theorems 3.9 and
3.10, Corollary 3.20, and Remark 3.22.

## 1. Standard words

Fix a natural unit interval order \(P\) on \([n]\). For a P-Knuth component
\(\Gamma\) and a set \(D\subseteq[n-1]\), let

\[
  \mathcal W(\Gamma,D)
  \coloneqq
  \{w\in\Gamma:\operatorname{Des}_P(w)=D\}.
\]

We use the P-tableau convention of Blasiak--Eriksson--Pylyavskyy--Siegl in
this section. Thus their tableaux are the transpose of the
Shareshian--Wachs tableaux. Put

\[
  \mathcal Y(\Gamma,D)
  \coloneqq
  \{(U,V):
    \operatorname{colword}(U)\in\Gamma,\ 
    V\in\operatorname{SYT}(\operatorname{shape}(U)),\
    \operatorname{Des}(V)=D\}.
\]

Theorem 3.10 of the cited paper gives

\[
  \sum_{w\in\Gamma}F_{\operatorname{Des}_P(w)}
  =
  \sum_{\substack{U\text{ a P-tableau}\\
                    \operatorname{colword}(U)\in\Gamma}}
    s_{\operatorname{shape}(U)}.
\]

Expanding each Schur function in the fundamental basis shows that

\[
  |\mathcal W(\Gamma,D)|=|\mathcal Y(\Gamma,D)|
\]

for every pair \((\Gamma,D)\). Order the words lexicographically. Order the
pairs lexicographically by the shape, the vector recording the
Shareshian--Wachs row of each label in \(U^{\mathsf t}\), and the row word of
\(V\). We map the \(r\)-th word to the \(r\)-th pair. This defines a
bijection

\[
  \varphi_P:S_n\longrightarrow
  \bigsqcup_{\lambda\vdash n}
  \operatorname{P\text{-}Tab}_P(\lambda)
  \times\operatorname{SYT}(\lambda).
\]

The fixed lexicographic orders are part of the definition; no matching is
chosen during the execution of the map. The construction is global rather
than insertion-local.

For a natural unit interval order, the statistic
\(\operatorname{inv}_P(w)\) is constant on a P-Knuth component. If
\(\varphi_P(w)=(U,V)\), Corollary 3.20 and Remark 3.22 therefore give

\[
  \operatorname{inv}_P(w)
  =\operatorname{inv}_P(\operatorname{colword}(U)).
\]

After transposing \(U\), the right-hand side is
\(\operatorname{inv}_G(T)\) in the Shareshian--Wachs convention.

## 2. Repeated colors

Let \(\kappa:[n]\to[k]\) be a proper coloring with content
\(\mu=(\mu_1,\dotsc,\mu_k)\). Complement its colors by setting

\[
  \bar\kappa(v)=k+1-\kappa(v).
\]

Each color class of \(\bar\kappa\) is a chain in \(P\). Write each class in
decreasing P-order and concatenate the classes in increasing color order.
This gives a permutation \(w\). Its block lengths are
\((\mu_k,\dotsc,\mu_1)\), and every internal block position is a P-descent.
Moreover,

\[
  \operatorname{inv}_P(w)
  =\operatorname{des}(\bar\kappa)
  =\operatorname{asc}(\kappa).
\]

Apply the standard map and write \(\varphi_P(w)=(U,V)\). Let
\(T=U^{\mathsf t}\), in the Shareshian--Wachs convention, and let
\(W=V^{\mathsf t}\). Since

\[
  \operatorname{Des}(W)
  =[n-1]\setminus\operatorname{Des}(V),
\]

every descent of \(W\) is a boundary between the blocks of \(w\). Hence
\(W\) uniquely destandardizes to a semistandard tableau \(Q'\) of content
\((\mu_k,\dotsc,\mu_1)\).

Let \(\eta_k\) be the ordinary semistandard Schützenberger--Lusztig
involution. It preserves shape and reverses content. Define

\[
  \Phi_{P,k}(\kappa)
  \coloneqq (T,Q),
  \qquad Q=\eta_k(Q').
\]

It follows that

\[
  \operatorname{wt}(Q)=\operatorname{wt}(\kappa),
  \qquad
  \operatorname{inv}_G(T)=\operatorname{asc}(\kappa).
\]

The inverse is explicit. Starting from \((T,Q)\), apply \(\eta_k\) to \(Q\).
Standardize equal entries from southwest to northeast, transpose the result,
and use the inverse lexicographic rank in the corresponding
\((\Gamma,D)\)-fiber. Split the recovered word into blocks of lengths
\((\mu_k,\dotsc,\mu_1)\), assign the complemented colors, and complement the
colors once more. The internal descent condition ensures that every block is
a decreasing P-chain. Standardization and destandardization are inverse,
\(\eta_k\) is an involution, and the two finite rank matchings are inverse.
Thus \(\Phi_{P,k}\) is a bijection.

## 3. The direct crystal

The ordinary Kashiwara operators now transport without a signed set:

\[
  e_i^P
  =\Phi_{P,k}^{-1}\circ(1\times e_i)\circ\Phi_{P,k},
  \qquad
  f_i^P
  =\Phi_{P,k}^{-1}\circ(1\times f_i)\circ\Phi_{P,k}.
\]

These operators preserve \(T\), properness, and the ascent statistic. Each
connected component is a normal type-A crystal \(B_k(\lambda)\), indexed by
a Shareshian--Wachs P-tableau \(T\) of shape \(\lambda\). This construction
also defines the simple reflections and satisfies the braid relations.

This proves existence of a direct normal crystal on colorings. An intrinsic
local description remains open because the rank matching defining
\(\varphi_P\) examines a whole P-Knuth component.

## 4. Exact finite verification

The Rust prototype is in experiments/chromatic-p-array-rsk/src/main.rs. It
implements Definition 3.2 of the cited paper, constructs every standard
P-Knuth component, verifies the fundamental-descent inventory in every
component, and builds both directions of the rank matching.

For every natural unit interval order through rank five, the program checks:

- the standard map and its inverse on all permutations;
- the repeated-color map and its inverse on every proper coloring with
  alphabet \([n]\);
- exact coverage of every target fiber;
- preservation of weight and
  \(\operatorname{asc}(\kappa)=\operatorname{inv}_G(T)\);
- all transported lowering edges and their raising inverses.

The census is:

| \(n\) | posets | P-Knuth components | P-tableau anchors | anchor excess | full-alphabet colorings | lowering edges |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 1 | 1 | 0 | 1 | 0 |
| 2 | 2 | 4 | 4 | 0 | 6 | 2 |
| 3 | 5 | 23 | 23 | 0 | 81 | 68 |
| 4 | 14 | 187 | 188 | 1 | 1,780 | 2,322 |
| 5 | 42 | 1,820 | 1,849 | 29 | 55,125 | 96,968 |

Only one rank-four component and 21 rank-five components contain more than
one P-tableau anchor. Thus the difference between P-Knuth components and
crystal components is concentrated in a small exceptional set at these
ranks. The direct map differs from the Allen--Celano--Mason signed map on
39,666 of the 55,125 rank-five colorings, so it defines a third crystal
gauge.

## 5. The first local correction

For the forbidden order with Hessenberg code \((2,4,4,5,5)\), the component
containing the Kim--Pylyavskyy word \(34521\) has 19 permutations and Schur
content

\[
  2s_{41}+s_{32}+s_{311}.
\]

Its P-tableau column words are

\[
  31542,51423\quad(4,1),
  \qquad 52413\quad(3,2),
  \qquad 53142\quad(3,1,1).
\]

Kim--Pylyavskyy insertion is valid on 17 of these 19 permutations. The two
words \(35241\) and \(34521\) give the same invalid insertion tableau

\[
  \begin{array}{ccc}3&1&2\\5&4\end{array}.
\]

Replacing it by

\[
  \begin{array}{ccc}2&1&3\\5&4\end{array}
\]

and retaining the recording tableau fills the two missing recording tableaux
in the shape-\((3,2)\) fiber. The new insertion tableau has column word
\(52413\). This gives an exact repair in rank five.

The complete Kim--Pylyavskyy trace and inverse are now implemented.  In rank
six there are 112 bad insertion tableaux on the 12 ladder-climbing orders.
The forced missing targets fall into ten cell actions; six actions change both
shape and recording tableau.  A 77-signature guarded rewrite and its separately
checked inverse give a bijection through rank six.  Kim--Pylyavskyy Example
7.11 produces a nonpartition column-height composition in rank seven, so this
finite rule is not yet an all-rank insertion.  The algorithms, censuses, and
exact obstructions are recorded in
[LOCAL_KP_INSERTION.md](LOCAL_KP_INSERTION.md).

## 6. Closed and secondary avenues

A standalone inverse-Kostka differential cannot commute with the Kashiwara
operators. Already

\[
  m_{(2)}=s_{(2)}-s_{(1,1)}
\]

forces the weight-\((1,1)\) cancellation to pair the row tableau \(12\) with
the column tableau \(1/2\). The operator \(f_1\) sends the row tableau to
\(22\) and is undefined on the column tableau. This obstruction applies to
every basis-preserving inverse-Kostka cancellation, not only the two
implemented involutions.

The combined Shareshian--Wachs and inverse-Kostka alternating graph has a
two-term incidence complex on each endpoint path. It may explain correction
terms by chain homotopies, but it is no longer needed for existence of the
direct bijection. It remains a diagnostic for comparing the three crystal
gauges.
