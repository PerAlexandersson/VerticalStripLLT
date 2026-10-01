---
title: Elementary expansions of circular LLT polynomials and flip components
abstract: |
  We prove an elementary expansion for circular LLT polynomials after the
  substitution $q\mapsto q+1$. The terms are indexed by acyclic selections
  of edges, and their elementary factors record highest reachable vertices
  on the integer cover. We also prove that the expansion holds separately
  on every circular component under triangle flips. Both arguments
  use local diagram relations. In the circular case, intersecting bounce
  paths are reduced by reversing intervals in a strict chain. In the
  ordinary case, actual flip paths connect the states in which every
  corner is a cover, and an endpoint attachment extends the component
  recurrence across articulations. A finite signed expansion then reduces
  circular components to unions of ordinary components. As a corollary,
  we obtain a componentwise elementary expansion for circular LLT cumulants.
---

# Introduction

The elementary expansion of a vertical-strip LLT polynomial can be read
from directed paths in its natural unit-interval graph. We retain every
strict edge and choose a subset of the normal edges. The highest vertex
reachable from each vertex determines a set partition, and the sizes of
its blocks give an elementary symmetric function. The formula of
P. Alexandersson and R. Sulzgruber [@AS22] expresses the LLT polynomial
after $q\mapsto q+1$ as the sum of these terms, weighted by the number
of chosen normal edges.
We extend this formula to circular diagrams and prove that it holds
separately on every component under local triangle flips.

LLT polynomials are closely related to chromatic quasisymmetric functions.
For an ordinary natural unit-interval graph $D$ without strict edges, the
unicellular LLT polynomial $G_D(X;q)$ sums $q^{\operatorname{asc}(\kappa)}x_\kappa$
over all vertex colorings, whereas the chromatic quasisymmetric function
$X_D(X;q)$ restricts this sum to proper colorings. Here an ascent is an edge
$u\to v$ with $\kappa(u)<\kappa(v)$, and
$x_\kappa=\prod_u x_{\kappa(u)}$. The plethystic identity

\[
 X_D(X;q)=(q-1)^{-n}G_D[(q-1)X;q]
 \tag{chromatic}
\]

relates the two functions on $n$ vertices [@AS22, Lemma 6.17]. The brackets
denote plethysm in the alphabet: on the power sums,
$p_r[(q-1)X]=(q^r-1)p_r(X)$. In particular, the Dyck-path bounce relations
and multiplicativity are the same for the two families; their initial
values on path graphs differ [@AS22, Corollary 6.18]. This common recursion
explains why diagram identities for LLT polynomials also arise in the
study of chromatic quasisymmetric functions.

A component refinement also arises on the chromatic side.
B.-H. Hwang [@Hwa22, Section 3] partitions heaps associated with proper
colorings into classes under local flips. A flip reverses a two-edge
fork whose edges are covers. These classes refine the ascent statistic
[@Hwa22, Proposition 3.7],
and their chromatic contributions are symmetric and Schur-positive
[@Hwa22, Theorems 3.8 and 4.19]. Hwang conjectures elementary positivity
for these contributions; in his weak-coloring convention this is stated
as complete homogeneous positivity [@Hwa22, Conjecture 3.10]. He also
asks for an analogous positive refinement of LLT polynomials
[@Hwa22, Section 5.3]. Our component theorem gives an elementary
expansion for the LLT triangle-flip components defined below.
These flips act on selected edges of the natural diagram, while Hwang's
flips act on heaps of proper colorings.

We first treat the circular extension. There is no largest vertex on the circle,
so we lift the selected edges to the integers, take the greatest
reachable integer, and reduce modulo the period. Acyclicity on the
residues makes this maximum finite. If $D$ is a circular diagram with
strict set $S$, our first result is the following. This requires a direct
LLT argument: the ordinary plethystic identity (chromatic) fails in the
circular setting [@AS22, Section 6.8].

::: {.theorem #thm:introCircular title="Circular elementary expansion"}
For every circular decorated diagram $D$,

\[
 G_D(X;q+1)=
 \sum_{A\text{ admissible}}q^{|A\setminus S|}e_{\lambda(A)}(X),
\]

where $\lambda(A)$ consists of the sizes of the fibres of this highest
reachable map. Thus the circular polynomials also have nonnegative
elementary coefficients after the shift.
:::

Our second result refines the expansion component by component, for
ordinary and circular diagrams alike. A triangle flip exchanges one
short selected edge for the other, retaining the long edge, when the
indicated edges are covers on the integer lift. Such flips partition the
selected states into components. For a selected state $A$, let $K(A;X)$
be the sum of monomials over colorings that increase strictly along
every selected edge.

::: {.theorem #thm:introComponent title="Component elementary expansion"}
For every ordinary or circular decorated diagram and each whole flip
component $C$ of admissible selected states,

\[
                  \sum_{A\in C}K(A;X)
                    =\sum_{A\in C}e_{\lambda(A)}(X).
\]
:::

In particular, the colorings become symmetric after summing over a
single component. The coefficient of $e_\lambda$ is the number of its
states whose highest reachable fibres have sizes $\lambda$. Since a
flip preserves the number of selected normal edges, multiplying by the
common power of $q$ gives the corresponding contribution to the shifted
LLT polynomial.

This positivity is a refinement of the LLT expansion. Applying the
ordinary plethystic transformation does not give positive chromatic
contributions term by term: already
$(q-1)^{-1}e_2[(q-1)X]=(q+1)e_2(X)-e_1(X)^2$.
Thus the common diagram relations and the two component constructions
provide related approaches to positivity, while the generating functions
and local moves remain distinct.

The two proofs have a common starting point. We use diagrams to describe
sums over selections. Blank cells
are optional edges; selected, absent and strict entries impose the
corresponding restrictions. A local identity can therefore retain all
exterior choices. The four relations, namely corner resolution and the NN,
DN, and ND bounce relations, are collected in
Proposition~\ref{prop:fourRecurrences}. We prove that the coloring and
highest reachable sums satisfy each relation. In the first part, these
identities reduce both sums to the same products of elementary functions
on strict chains. The circular obstruction is that bounce paths may
intersect. Reversing consecutive intervals in their common strict chain
and removing internal edges with known factors reduces these intersections
to smaller diagrams as well.

For ordinary components, we need actual paths of flips as well as
identities between sums. Starting from a state in which every corner is
a cover, we prepare its selected edges and use crossing slides to
rearrange them while restoring the exterior. These paths show that the
relevant connected states of each selected size lie in one component.
We can then complete a component
to a full edge layer, apply a diagram relation, and subtract the other
components using smaller diagrams. Fixing the color at an endpoint
allows the recurrence to be attached to the rest of the diagram.

To pass to circular components, we expand a selected graph into balanced
subgraphs, whose edge lengths are differences of a vertex potential.
The same signed coefficients work for the coloring and HRV values, and
remain constant along whole flip components. Sorting compatible lifts
then represents each balanced circular component by a union of ordinary
components. This reduces the circular statement to the ordinary diagram
proof.

The final application is to LLT cumulants. Their defining alternating sum
over set partitions retains precisely those selected graphs which connect
the prescribed vertex classes. This is the connected-subgraph principle
of M. Dołęga and M. Kowalski [@DK22, Theorem 3.8]. Connectivity is constant
on a flip component, so the component theorem applies to the retained
terms. Corollary~\ref{cor:cumulantComponent} gives the circular cumulant
expansion and refines its ordinary counterpart [@DK22, Theorem 3.17]
component by component.

The paper follows this order: the circular expansion and its four local
relations, the ordinary component proof and its passage to the circle,
and the cumulant corollary. Throughout we use a finite alphabet
$X=(x_1,\dotsc,x_m)$ and write

\[
 e_r(X)=\sum_{1\leq i_1<\dotsb<i_r\leq m}x_{i_1}\dotsm x_{i_r},
 \qquad e_0(X)=1,
 \qquad e_\lambda(X)=\prod_j e_{\lambda_j}(X).
\]

The identities hold for every alphabet size and therefore give the
corresponding symmetric-function identities.
