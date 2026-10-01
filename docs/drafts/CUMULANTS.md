# LLT cumulants

We record the cumulant consequence of the component identity. The
set-partition cancellation is the connected-subgraph argument for LLT
cumulants in [@DK22, Theorem 3.8]; in the ordinary case, the resulting
connected orientation expansion is the formula of [@DK22, Theorem 3.17].
We use the same argument for circular diagrams and then group the states by
flip components.

::: {.lemma #lem:cumulantInducedRestriction title="Induced restriction"}
Let \(D\) be a circular decorated diagram and let \(U\) be a nonempty subset
of its residues. The induced diagram \(D[U]\), with the inherited cyclic
order, is again a circular decorated diagram. If an admissible state of $D[U]$
has no selected edge between distinct blocks of a partition of \(U\), then
its highest-reachable partition is the concatenation of the
highest-reachable partitions of the induced restrictions.
:::

::: {.proof}
List the retained residues by increasing periodic lifts
\((u_j)_{j\in\mathbb Z}\), with \(u_{j+m}=u_j+n\), where \(m=|U|\). If
\(b_i\) denotes the beginning of row \(i\), define the beginning of compressed
row \(j\) by
\[
 b'_j=\min\{k:u_k\ge b_{u_j}\}.
\]
The sequence \(b'_j\) is nondecreasing, satisfies
\(j-m<b'_j\le j\), and obeys \(b'_{j+m}=b'_j+m\), so it defines the
induced circular diagram. A surviving strict corner remains strict: if
\(u_k\to u_j\) is strict, then \(b_{u_j}=u_k\) and
\(b_{u_j+1}>u_k\), hence \(b'_j=k<b'_{j+1}\).

Compression preserves the order and intertwines translation by \(n\) with
translation by \(m\). Thus natural lifted edges and paths correspond. If no
selected edge joins two blocks, every reachable lift remains in the block of
its starting vertex. Compression therefore preserves the highest reachable
lift and the sizes of all highest-reachable fibres, which proves the claim.
:::

::: {.definition #def:cumulant title="Normalized LLT cumulant"}
Let \(r\geq1\), let \(D=(E,S)\) be a circular decorated diagram, and let
\(f:V(D)\twoheadrightarrow[r]\) be surjective and constant on the endpoints
of every strict edge. For each nonempty \(B\subseteq[r]\), let \(D_B\) be the
induced diagram on \(f^{-1}(B)\), with inherited cyclic order. Let
$\Pi([r])$ be the set of partitions of $[r]$, ordered by refinement,
with greatest element $\widehat1=\{[r]\}$. Define the
\defin{normalized LLT cumulant} by
\[
\defin{\kappa_{D,f}(X;t)}
=(t-1)^{1-r}\sum_{\pi\in\Pi([r])}
(-1)^{|\pi|-1}(|\pi|-1)!
\prod_{B\in\pi}G_{D_B}(X;t).
\]
:::

For an admissible state \(A\), let \(A/f\) be the quotient multigraph on
\([r]\), retaining loops and edge instances. We call \(A\)
\defin{$f$-connected} when the underlying undirected graph of \(A/f\) is connected,
with all \(r\) color classes retained, including isolated classes. Let
\(\sigma_f(A)\) be the set partition of \([r]\) into the weak components of
\(A/f\). Thus \(A\) is \(f\)-connected exactly when
\(\sigma_f(A)=\widehat 1\).

::: {.proposition #prop:cumulantConnectedExpansion title="Connected orientation expansion"}
With the notation above,
\[
\kappa_{D,f}(X;1+q)
=\sum_{\substack{A\text{ admissible}\\A\text{ is }f\text{-connected}}}
q^{|A\setminus S|+1-r}\mathsf{K}(A).
\]
Every exponent on the right is nonnegative.
:::

::: {.proof}
For \(\pi\in\Pi([r])\), apply the shifted exact expansion to every induced
diagram \(D_B\). Combining the selected states from the blocks, while leaving
all cross-block non-strict edges inactive, gives
\[
\prod_{B\in\pi}G_{D_B}(X;1+q)
=\sum_{\substack{A\text{ admissible}\\\sigma_f(A)\le\pi}}
q^{|A\setminus S|}\mathsf{K}(A).
\]
The strict-edge hypothesis ensures that no strict edge crosses the blocks.
After inserting this identity into the cumulant definition, the coefficient
of a fixed state \(A\) is
\[
q^{|A\setminus S|+1-r}
\sum_{\sigma_f(A)\le\pi\le\widehat1}
(-1)^{|\pi|-1}(|\pi|-1)!
=q^{|A\setminus S|+1-r}
\mathbf 1_{\{\sigma_f(A)=\widehat1\}},
\]
by Möbius inversion in the set-partition lattice. This proves the displayed
expansion, initially as a Laurent-polynomial identity.

Every strict edge becomes a loop in \(A/f\). Since an \(f\)-connected quotient
on \(r\) vertices needs at least \(r-1\) selected non-strict edges,
\(|A\setminus S|\ge r-1\), proving nonnegativity.
:::

::: {.lemma #lem:cumulantFlipInvariant title="Cumulant connectivity is flip-invariant"}
The property of being \(f\)-connected is constant on every complete circular
flip component. The number \(|A\setminus S|\) is constant on such a component.
:::

::: {.proof}
A flip preserves the weak-component partition of the selected graph,
so passing to the quotient by \(f\) preserves \(\sigma_f(A)\). It also
exchanges one selected non-strict edge for another, preserving
\(|A\setminus S|\). Both assertions therefore hold along every flip path.
:::

::: {.corollary #cor:cumulantComponent title="Component refinement of LLT cumulants"}
Let \(\mathfrak C_f(D)\) be the set of complete circular flip components
consisting of \(f\)-connected admissible states. For \(C\in\mathfrak C_f(D)\),
write \(d_C=|A\setminus S|\) for any \(A\in C\). Then
\[
\kappa_{D,f}(X;1+q)
=\sum_{C\in\mathfrak C_f(D)}
q^{d_C+1-r}\sum_{A\in C}e_{\lambda(A)}(X).
\]
Each component contribution is \(e\)-positive over \(\mathbb N[q]\).
:::

::: {.proof}
By Lemma~\ref{lem:cumulantFlipInvariant}, the connected states in
Proposition~\ref{prop:cumulantConnectedExpansion} are a
disjoint union of the components \(C\in\mathfrak C_f(D)\), and the exponent
is constant on each component. Grouping the connected orientation expansion
by these components gives
\[
\kappa_{D,f}(X;1+q)
=\sum_{C\in\mathfrak C_f(D)}
q^{d_C+1-r}\sum_{A\in C}\mathsf{K}(A).
\]
Apply Theorem~\ref{thm:circularComponent} to each inner sum:
\[
\sum_{A\in C}\mathsf{K}(A)=\sum_{A\in C}e_{\lambda(A)}(X).
\]
The exponents are nonnegative by the connected orientation proposition, and
each inner sum is an elementary-positive symmetric function.
:::
