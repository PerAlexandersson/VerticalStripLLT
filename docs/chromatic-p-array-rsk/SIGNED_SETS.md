# Chromatic generalized RSK: signed sets and involutions

This note fixes the finite objects needed for a Garsia--Milne prototype.  It
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
1990 inverse-Kostka paper and Allen--Celano--Mason, arXiv:2511.18156; these
distinguish the two matrix orders that a formal symmetric-function identity
alone can easily conceal.

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
Allen--Celano--Mason, arXiv:2511.18156, gave a full construction for
the reverse identity using the Garsia--Milne involution principle.

Consequently, the ordinary LGV tail switch proving Jacobi--Trudi is not
by itself the second involution needed below.  Importing the full
inverse-Kostka involution is one option.  For a bounded experiment, we
can instead pair the positive and negative elements of

\[
  \bigsqcup_{\lambda\vdash n}
  \mathcal J_{\lambda,\nu}
  \times\operatorname{SSYT}(\lambda,\mu)
\]

in lexicographic order, leaving one canonical positive fixed point
when (\nu=\mu).  This finite matching is explicit and reversible,
although it is not a local tableau algorithm.

## 5. The common signed set

Fix a packed weight (\mu\vDash n), and write (\bar\mu=\mu^+) for its
decreasing rearrangement.  Its positive parts need not be weakly decreasing;
the Bender--Knuth maps identify its Kostka number with that of
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
Garsia--Milne map.  Every step is reversible.  A trace needs only the
signed states, the selected bad cell or inverse-Kostka matching rank,
and the adjacent-swap words used by the normalizations.

## 6. Converting ascent to the array inversion statistic

The array involution preserves descent number, while the requested map
starts with ascent number.  For a packed coloring of weight
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
P-Knuth equivalence preserves the fake (P)-inversion statistic.  We
shall use this correspondence as an oracle on its avoidance class; it
does not supply a generalized correspondence for repeated colors.

## 8. First computational questions

The bounded prototype should answer the following questions for every natural
unit interval order with (n\leq5).

1. Do the source and target fibers agree for every packed weight and every
   (q)-degree?
2. Does the conjugated Shareshian--Wachs involution close on
   (\mathcal S_\mu) and preserve its recorded degree?
3. How long are the alternating paths when the reverse inverse-Kostka
   involution is the canonical finite matching?
4. What is the first state for which a naive attempt to replace that matching
   by a synchronized LGV tail switch fails to close?
5. On the Kim--Pylyavskyy avoidance class, does standardizing a packed
   coloring and destandardizing the recording tableau reproduce the same
   fibers?  Any failure must be retained as an exact counterexample.
