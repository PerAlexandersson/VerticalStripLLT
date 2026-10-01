---
title: Elementary expansions of circular LLT polynomials and ordinary flip components
abstract: |
  We prove an elementary expansion for circular LLT polynomials after the
  substitution $q\mapsto q+1$. The terms are indexed by acyclic selections
  of edges, and their elementary factors record highest reachable vertices
  on the integer cover. For ordinary diagrams, we prove that the expansion
  holds separately on each component under triangle flips. Both arguments
  use local diagram relations. In the circular case, intersecting bounce
  paths are reduced by reversing intervals in a strict chain. In the
  ordinary case, actual flip paths connect the states in which every
  corner is a cover, and an endpoint attachment extends the component
  recurrence across articulations.
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

We study two extensions of this formula. First, we allow the natural
diagram to be circular. There is then no largest vertex on the circle,
so we lift the selected edges to the integers, take the greatest
reachable integer, and reduce modulo the period. Acyclicity on the
residues makes this maximum finite. If $D$ is a circular diagram with
strict set $S$, our first result is

\[
 G_D(X;q+1)=
 \sum_{A\text{ admissible}}q^{|A\setminus S|}e_{\lambda(A)}(X),
\]

where $\lambda(A)$ consists of the sizes of the fibres of this highest
reachable map. Thus the circular polynomials also have nonnegative
elementary coefficients after the shift.

Our second result refines the ordinary expansion. A triangle flip
exchanges one short selected edge for the other, retaining the long
edge, when the indicated edges are covers. Such flips partition the
selected states into components. For a selected state $A$, let $K(A;X)$
be the sum of monomials over colorings that increase strictly along
every selected edge. We prove, for each whole flip component $C$,

\[
                  \sum_{A\in C}K(A;X)
                    =\sum_{A\in C}e_{\lambda(A)}(X).
\]

In particular, the colorings become symmetric after summing over a
single component. The coefficient of $e_\lambda$ is the number of its
states whose highest reachable fibres have sizes $\lambda$. Since a
flip preserves the number of selected normal edges, multiplying by the
common power of $q$ gives the corresponding contribution to the shifted
LLT polynomial.

The proofs use diagrams to describe sums over selections. Blank cells
are optional edges; selected, absent and strict entries impose the
corresponding restrictions. A local identity can therefore retain all
exterior choices. For circular diagrams, the coloring and highest
reachable sums satisfy the same corner and bounce relations. When
bounce paths intersect, we reverse consecutive intervals within their
common strict chain. After removing internal edges with known factors,
this identifies both sums with those of a smaller diagram.

For ordinary components, we need actual paths of flips as well as
identities between sums. Starting from a state in which every corner is
a cover, we prepare its selected edges and use crossing slides to
rearrange them while restoring the exterior. These paths prove uniqueness at each selected
size for connected common-cover states. We can then complete a component
to a full edge layer, apply a diagram relation, and subtract the other
components using smaller diagrams. Fixing the color at an endpoint
allows the recurrence to be attached to the rest of the diagram.

We first prove the circular expansion, including the reductions for
intersecting contact paths. We then give the ordinary component proof,
with its flip constructions and endpoint attachment. Throughout we use
a finite alphabet $X=(x_1,\dotsc,x_m)$ and write

\[
 e_r(X)=\sum_{1\leq i_1<\dotsb<i_r\leq m}x_{i_1}\dotsm x_{i_r},
 \qquad e_0(X)=1,
 \qquad e_\lambda(X)=\prod_j e_{\lambda_j}(X).
\]

The identities hold for every alphabet size and therefore give the
corresponding symmetric-function identities.
