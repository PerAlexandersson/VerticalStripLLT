# The circular elementary expansion

We prove the circular expansion by showing that the coloring sum and the
highest-reachable sum satisfy the same recurrences and the same initial
values. The argument has three steps. We recall the ordinary relations of
Alexandersson--Sulzgruber and put them in the shifted form used here. We then
prove those relations directly on the integer cover, including the extra
cases in which circular bounce paths intersect. Finally, we orient the
relations so that every final term is smaller in a specified induction
order. The initial diagrams are disjoint strict chains, for which both sums
are products of elementary symmetric functions.

## Circular diagrams and highest reachable vertices

::: {.definition #def:circularDiagram title="Circular decorated diagram"}
Let $n\geq1$, and let $(a_0,\ldots,a_{n-1})$ satisfy
$0\leq a_i<n$ and $a_{i+1}\leq a_i+1$, with subscripts modulo $n$.
We extend the sequence periodically and put $\defin{b(i)}\coloneqq i-a_i$.
The natural edges in row $i$ are

\[
                 b(i)\longrightarrow i,\quad\ldots,\quad i-1\longrightarrow i.
\]

We identify integer translates by $n$. A natural edge retains its positive
lift, of length less than $n$. In particular, opposite edges between two
residues are distinct. The first edge in row $i$ is a corner when
$a_i>0$ and $b(i+1)>b(i)$. We may mark any subset $S$ of the corners
strict. We denote the resulting \defin{circular decorated diagram} by $D$.
:::

::: {.definition #def:circularLLT title="Coloring LLT polynomial"}
For a finite alphabet $X=(x_1,\ldots,x_m)$, define

\[
 \defin{G_D(X;q)}\coloneqq
 \sum_{\substack{\kappa:\mathbb Z/n\mathbb Z\to\{1,\ldots,m\}\\
       uv\in S\Rightarrow\kappa(u)<\kappa(v)}}
 q^{\#\{uv\notin S:\kappa(u)<\kappa(v)\}}
 \prod_u x_{\kappa(u)}.
\]
:::

::: {.definition #def:circularHRV title="Selected states and highest reachable vertices"}
A \defin{selected state} $A$ contains all strict edges and any subset of the
remaining natural edges. We call $A$ \defin{admissible} when its directed graph
on residues is acyclic. For an integer $u$, let

\[
 \defin{\widetilde H_A(u)}\coloneqq
 \max\{v\in\mathbb Z:v\text{ is reachable from }u\text{ in the lift of }A\}.
\]

We allow paths of length zero. A path cannot repeat a residue, so this
maximum exists. Moreover, $\widetilde H_A(u+n)=\widetilde H_A(u)+n$.
Its residue defines a map $H_A$ on the vertices of the circular diagram.
Let $\lambda(A)$ be the partition of the sizes of its nonempty fibres,
and put

\[
 \defin{\widehat G_D(X;q)}\coloneqq
 \sum_{A\text{ admissible}}q^{|A\setminus S|}e_{\lambda(A)}(X).
\]
:::

::: {.example #ex:directedCycle title="A directed three-cycle"}
For example, take $(a_0,a_1,a_2)=(1,1,1)$ with no strict corners.
The natural edges form the directed cycle $0\to1\to2\to0$.
The selected path $2\to0\to1$ lifts to $2\to3\to4$.
All three vertices therefore have highest reachable residue $1$.
The empty selection, the three single edges and the three two-edge
paths give

\[
 \widehat G_D(X;q)=e_1(X)^3+3q e_2(X)e_1(X)+3q^2e_3(X).
\]
:::

::: {.theorem #thm:circularExpansion title="Circular elementary expansion"}
For every circular decorated diagram,

\[
                 G_D(X;q+1)=\widehat G_D(X;q).
\]

Thus the shifted polynomial has nonnegative coefficients in the elementary
basis. The identity holds for every finite alphabet and hence
coefficientwise in infinitely many variables.
:::

We prove Theorem~\ref{thm:circularExpansion} by showing that its two sides
satisfy the same local relations and initial values. The four relations
are stated together below; the remaining subsections prove them and treat
the additional contact configurations that arise on a circle.

## The local reductions

::: {.definition #def:bounceContacts title="Bounce contacts"}
Write $s(i)$ for the strict flag in row $i$ and
$g(i)\coloneqq b(i+1)-b(i)-s(i)$ for the number of east steps after
that row. A bounce starts at a strict row $t$ with $a_t\geq2$ and
$g(t)>0$. Its first lower contact is $x=b(t)$. At a contact with
$g(x)=0$, the flags $s(x),s(x+1)$ specify NN, DN, ND or DD.
A DD contact continues the bounce backwards along the strict path.
We write $\mathtt n,\mathtt d,\mathtt e$ for north, diagonal and east
steps of the boundary path in the integer lift.
:::

### The relations of Alexandersson--Sulzgruber

We first recall the relations before shifting the parameter. In the
following display, $G_P$ means $G_P(X;q)$, and $U,V,W$ are unchanged
path words. We first display the one-contact ordinary cases: the indicated
occurrences form the bounce decomposition of a Schröder path, with just one
bounce point. The two contact vertices are consecutive and distinct from
the terminal vertex. Theorem 2.5 of [@AS22] also gives the extension to
several bounce points. Below we prove the extension needed on the circle.

::: {.proposition #prop:originalRecurrences title="Alexandersson--Sulzgruber relations"}
The ordinary LLT polynomials satisfy [@AS22, Theorems 2.1 and 2.5]
\[
\begin{aligned}
 G_{U\mathtt{ne}V}-G_{U\mathtt{en}V}
   &=(q-1)G_{U\mathtt dV}, &&\text{(corner)},\\
 G_{U\mathtt{nn}V\mathtt{de}W}
   &=qG_{U\mathtt{nn}V\mathtt{ed}W}, &&\text{(NN)},\\
 G_{U\mathtt{dn}V\mathtt{de}W}
   &=G_{U\mathtt{nd}V\mathtt{ed}W}, &&\text{(DN)},\\
 G_{U\mathtt{nd}V\mathtt{de}W}
   &=(q-1)G_{U\mathtt{nd}V\mathtt{ed}W}
     +qG_{U\mathtt{dn}V\mathtt{ed}W}, &&\text{(ND)}.
\end{aligned}                                                    \tag{AS}
\]
Their initial values and product rule are
\[
 G_{\mathtt n\mathtt d^k\mathtt e}=e_{k+1}(X),
 \qquad G_{PQ}=G_PG_Q.
\]
:::

In the presence of corner resolution, the NN and DN relations are
equivalent to the NN and ND relations [@AS22, Proposition 3.1]. This lets
us choose the relation in the direction needed for induction. The original
uniqueness proof inducts on the path size, the number of east steps, and
the height of the first east step. We use an order suited to the circular
extension and, later, a separate order for component reductions.

### Shifted relations and the induction order

From now on, $F_D$ denotes either $G_D(X;q+1)$ or the proposed elementary
sum $\widehat G_D(X;q)$. Substituting $q+1$ for $q$ in (AS) gives the
ordinary one-contact instances of the four relations below. The change of
parameter is reversible; extending the relations across a circular cut and
dealing with intersecting contact paths still require proof.

For corner resolution, let $D^-$ delete a non-strict corner and let
$D^{\mathrm s}$ mark it strict. For a bounce with $k$ intervening DD
contacts, let $x=b^{k+1}(t)$ be its final lower contact. The NN target
shortens the terminal strict edge by one. The DN target also moves the
initial strict head from $x$ to $x+1$, increasing $a_{x+1}$ by one.
For ND, let $Q$ only shorten the terminal strict edge; let $R$ also
move the initial strict head from $x+1$ to $x$, decreasing $a_{x+1}$
by one. All changes are periodic, and all exterior data remain fixed.

::: {.proposition #prop:fourRecurrences title="The four local recurrences"}
Both $F_D=G_D(X;q+1)$ and $F_D=\widehat G_D(X;q)$ satisfy corner
resolution and the following three bounce relations:

\[
 \begin{aligned}
 F_D&=F_{D^-}+qF_{D^{\mathrm s}}
       &&\text{(corner)},\\
 F_{U\mathtt{nn}V\mathtt{de}W}
    &=(1+q)F_{U\mathtt{nn}V\mathtt{ed}W}
       &&\text{(NN)},\\
 F_{U\mathtt{dn}V\mathtt{de}W}
    &=F_{U\mathtt{nd}V\mathtt{ed}W}
       &&\text{(DN)},\\
 F_D&=qF_Q+(1+q)F_R
       &&\text{(ND)}.
 \end{aligned}                                                   \tag{R}
\]

For the bounce relations the terminal row is strict with $a_t\geq2$
and $g(t)>0$, the intervening contacts are DD, and the final contact
has the indicated flags. The strict graph of the source is acyclic.
For ND we additionally require
$b^i(t)\not\equiv x+1\pmod n$ for $0\leq i\leq k$.
In ordinary diagrams this separation is automatic. Circular ND contacts
that fail it are treated by Propositions~\ref{prop:terminalContact}
and~\ref{prop:columnReversal}.
:::

Their ordinary one-contact specializations are the shifted corner and
bounce relations of [@AS22, Theorem 2.5]. We retain their diagram interpretation on the integer
cover. The extra separation condition records where circular contact
paths can meet. We prove corner resolution immediately, then NN and DN,
and finally derive ND from those relations.

![The four local recurrences as boundary-path diagrams](figures/circular-direct-relations.svg)

*Figure 1.* The four local recurrences. Gray lies outside the path;
zigzags stand for arbitrary unchanged portions. The vertices $x,y$ are
consecutive, whereas the interval before $z$ may contain other vertices.
The red line shows the bounce. Each picture denotes the full weighted sum,
with a factor $q$ for each selected non-strict edge. The displayed bounce
relations have one contact; the proof below removes intervening DD contacts.
For the HRV sum we retain admissible selections; cyclic selections have
coloring value zero.

The direction of reduction matters. Put
\[
 \mu(D)=2\sum_i a_i-|S|,\qquad
 \nu(D)=\sum_{e\in S}d(\operatorname{head}(e))\ell(e),             \tag{measure}
\]
where $\ell(e)$ is the positive length of a strict edge and $d(v)$ counts
its strict ancestors: vertices with a nonempty strict path to $v$.
Here $\sum_i a_i$ counts all natural edges, including strict edges.
We use lexicographic induction on $(\mu(D),\nu(D))$.

\begin{center}
\begin{tabular}{@{}ll@{}}
\toprule
Reduction & Change in the induction order \\
\midrule
Corner deletion or strict marking & $\mu$ decreases by two or one \\
NN & $\mu$ decreases by two \\
Forward DN & $\mu$ is unchanged and $\nu$ decreases \\
Separated ND & $\mu$ decreases by two and four \\
Terminal intersection & $\mu$ decreases by six \\
Interior intersection & Reversal decreases $\mu$ \\
\bottomrule
\end{tabular}
\end{center}

The local proofs below establish the identities first. In particular,
removing intervening DD contacts uses a separate induction on the number
of contacts; its temporary diagrams need not have smaller area. Only the
final targets in this table are used in the outer induction. The last
subsection verifies that every noninitial diagram admits one of these
reductions. This is what makes agreement of the two sums on the recurrences
and strict-chain products sufficient.

### Corner resolution and initial values

::: {.proof title="Proof of corner resolution"}
For colorings, the corner identity in (R) is the expansion of the corner weight
$1+q\,\mathbf1_{\kappa(u)<\kappa(v)}$. For selected states, we split
according to whether the corner is selected. In the selected term its
strict marking preserves reachability and removes one factor $q$.
:::

::: {.lemma #lem:circularInitialValues title="Initial values"}
A strict cycle makes both values of $F_D$ zero. If every natural edge
is strict and there is no cycle, both values equal
$\prod_B e_{|B|}(X)$, where $B$ runs through the strict chains,
including isolated vertices.
:::

::: {.proof}
Every vertex has at most one incoming and one outgoing strict edge.
Consequently the strict graph consists of chains and cycles. A strict
cycle forbids both a strict coloring and an admissible selected state.
On a chain the strict-coloring sum is $e_{|B|}$, and the highest
reachable map has that whole chain as one fibre. Distinct chains
contribute independently, giving the product.
:::


### Boundary symmetry and the coloring relations

::: {.lemma #lem:directColoringBounce title="Direct coloring relations"}
For a bounce with no intervening DD contacts, the coloring value
$G_D(X;q+1)$ satisfies the NN and DN identities in (R).
:::

::: {.proof}
Let $p=b(t)$ and write $\sigma$ for the periodic exchange of $p$ and
$p+1$. Thus $\sigma(p+kn)=p+1+kn$ and
$\sigma(p+1+kn)=p+kn$, and every other integer is fixed. The terminal
strict edge has length at least two, and its positive east gap gives

\[
                   b(t)=p,\qquad b(t+1)\geq p+2.
\]

By monotonicity and periodicity, no boundary value is congruent to
$p+1$ modulo $n$. At a direct NN contact, we also have
$b(p)=b(p+1)$. These two facts give the required exterior symmetry.
Indeed, the two incoming intervals agree below $p$, while an incoming
interval at any other head cannot separate the adjacent tails $p,p+1$:
its lower endpoint never equals $p+1$. The only order inversion is the
pair $p,p+1$ itself. After removing this normal edge and the two pairs
from $p,p+1$ to $t$, the natural background is invariant under $\sigma$.
For the coloring comparison we retain the normal edge $p(p+1)$ and
track its ascent separately. There is no strict head at either contact
vertex. A strict tail is a boundary value, so no strict edge leaves
$p+1$; strict-successor uniqueness leaves just the distinguished edge
from $p$ to $t$. Deleting that edge therefore leaves every strict
endpoint pair fixed by $\sigma$.

We now pair colorings. In the NN source, write the colors at $p,p+1,t$
as $a,b,c$, with $a<c$. If also $b<c$, keep the coloring. Otherwise
exchange the colors at $p,p+1$. The result is strict on the shortened
target edge $(p+1)t$, and the same rule in reverse recovers the source.
Exterior weights are unchanged by the symmetry just proved. If both
$a,b<c$, the normal edge $(p+1)t$ supplies one extra ascent in the
source. If $a<c\leq b$, the normal edge $p(p+1)$ supplies that extra
ascent before the exchange. In both cases the source has exactly one
more normal ascent. Its shifted coloring weight is therefore $1+q$
times the target weight, proving NN.

For DN, write the two strict edges as $up$ and $pt$, where
$a_p=a_{p+1}$. Temporarily delete the corner $up$. The two contact
boundaries then agree, the terminal gap still excludes the value $p+1$,
and there is no strict head at either contact vertex. The same argument
identifies the exterior background. In the source the distinguished
normal pair is $(p+1)t$; in the target it is $up$. The normal edge
$p(p+1)$ is present in both backgrounds.

For a source coloring, let the colors at $u,p,p+1,t$ be $a,b,c,d$,
so $a<b<d$. Keep the coloring if $a<c<d$; otherwise exchange $b,c$.
If both lie between $a,d$, the distinguished normal pair ascends on
both sides. If $c\leq a$, the source ascent on $(p+1)t$ is replaced
by the target ascent on $p(p+1)$. If $c\geq d$, the source ascent
on $p(p+1)$ is replaced by the target ascent on $up$. Thus the total
normal ascent count is unchanged. The exchange is invertible and proves
DN for the coloring sum.
:::

### The four selected triangles

::: {.lemma #lem:circularDiamond title="The four selected triangles"}
For the orientation calculation, consider the local triangle
$x<y<z<x+n$ in an NN or DN contact. The long edge $x\to z$ is
mandatory and the two shorts are permitted normal edges. Fix the exterior
selection and first leave both shorts absent. Write $m$ for its HRV
elementary monomial, $\ell$
when only the left short edge is added, $r$ when only the right short edge
is added, and $b$ when both are added. A cyclic selection has value zero.
The four selections satisfy

\[
 \ell+r
       =m+b.                     \tag{3}
\]

:::

::: {.proof}
We first note that adding $u\to v$ preserves the entire lifted HRV
map whenever $\widetilde H(v)\leq\widetilde H(u)$. The old HRV
function is nonincreasing along every old edge and along every periodic
copy of the added edge. Hence a new path starting at $w$ still ends at
or below $\widetilde H(w)$, and the old maximizing path is still
available. This also proves acyclicity: a directed cycle on residues
could be repeated in the lift to produce arbitrarily large endpoints.

If the bottom selection is cyclic, all four terms are zero. Otherwise
let $H$ be its lifted HRV map; the mandatory edge gives $H(z)\leq H(x)$.
We distinguish two cases.

If $H(y)\leq H(x)$, adding $x\to y$ changes nothing. If adding
$y\to z$ creates a cycle, the two terms containing that edge both
vanish. Otherwise a new path from $y$ either avoids the added edge or
starts with it: it cannot first return to another lift of $y$, since
that would give a cycle on residues. Its greatest endpoint is therefore
at most $\max(H(y),H(z))\leq H(x)$. Thus $x\to y$ is ineffective
after adding $y\to z$ as well. This pairs the bottom with the first
middle term and the other middle term with the top.

If $H(x)<H(y)$, the ineffective bottom edge is $y\to z$. After
adding $x\to y$, either both terms containing it vanish, or the
highest vertex reachable from $z$ stays $H(z)$. Indeed, a path from
$z$ cannot reach a lift of $x$, since the mandatory edge back to the
residue of $z$ would make a cycle. The HRV at $y$ can only increase,
so $y\to z$ remains ineffective. This gives the other pairing and
proves (3), including all cyclic cases.
:::

::: {.proof title="The direct NN and DN relations for highest reachable vertices"}
After inserting weights, (3) becomes

\[
 m+q(\ell+r)
       +q^2b
 =(1+q)(m+qb).
\]

The bottom terms in (R) correspond under the periodic exchange of the
contact vertices; the top terms have the same transitive closure.
Here $x,y$ are consecutive contact vertices. The exchange
preserves order on sinks: its only inverted pairs are $x+kn,x+1+kn$,
and the first vertex has the mandatory outgoing edge to $z+kn$.
Every reachable vertex extends to a sink. Thus the exchange transports
the highest reachable map and preserves its fibre sizes.
:::

### Removing intervening DD contacts

::: {.proof title="The NN and DN relations with intervening DD contacts"}
We prove the NN and DN identities in (R) by induction on the number of intervening DD contacts,
for both values of $F$ simultaneously. We assume the strict graph is
acyclic; strict cycles have already been treated. The case of no DD
contact is the local calculation above.

Suppose there is at least one DD contact. At the contact nearest the
terminal row $t$, put $p=b(t)$ and $u=b(p)$. Since $g(p)=0$ and both
$p,p+1$ are strict rows, the three strict edges there are

\[
             e:u\longrightarrow p,\qquad
             e':u+1\longrightarrow p+1,\qquad
             f:p\longrightarrow t.
\]

Write $h=a_p=a_{p+1}$ and $L=a_t$. We have $h,L\geq2$.
For $L$ this is terminal eligibility. For $h$, the corner at $p+1$
gives $b(p+2)>u+1$, while boundary monotonicity and $p+2\leq t$ give
$b(p+2)\leq b(t)=p$. Hence $u\leq p-2$.
In particular the five displayed integer vertices
are ordered $u<u+1<p<p+1<t$.

Unmark $e'$, then apply the direct DN relation to $e,f$; call the result
$R$. Alternatively, delete the corner $e'$ from $D$; call this diagram
$E$. Their changed rows are exactly as follows. An entry is the pair
$(\text{area},\text{strict flag})$; all other rows stay fixed.

| Diagram | Row $p$ | Row $p+1$ | Row $t$ |
| --- | --- | --- | --- |
| $D$ | $(h,1)$ | $(h,1)$ | $(L,1)$ |
| $R$ | $(h,0)$ | $(h+1,1)$ | $(L-1,1)$ |
| $E$ | $(h,1)$ | $(h-1,0)$ | $(L,1)$ |

Unmarking and deleting $e'$, followed by the direct DN identity, give

\[
                         qF_D=F_R-F_E.                         \tag{DD1}
\]

![One DD elimination as a difference of restricted sums](figures/circular-dd-elimination.svg)

*Figure 2.* We illustrate (DD1) with areas $(0,1,2,2,2)$ and strict
corners $02,13,24$. Thus $p=2$ and $t=4$. The resolved diagram has
areas $(0,1,2,3,1)$ and strict corners $03,34$; the deletion diagram
has areas $(0,1,2,1,2)$ and strict corners $02,24$. Each diagram sums
over all optional cells with weight $q^{|A\setminus S|}$. For the HRV
value we sum only admissible states; equivalently cyclic states have
value zero. For the coloring value we use the selected-edge expansion
of $G_D(X;q+1)$.

The new terminal row is $p+1$ in $R$ and $p$ in $E$. Both have a
positive east gap. In $E$, deleting $e'$ raises $b(p+1)$ by one, so the
gap after $p$ becomes positive. In $R$, the new boundary at $p+1$
is $u$, whereas the following boundary is greater than $u+1$.
The new terminal areas are $h+1$ and $h$, both at least two.
Moreover,

\[
                    b_R(p+1)=u=b_E(p).
\]

Thus both child bounces resume at the next old contact. Every subsequent
contact and its two flags stay unchanged, so each child has one fewer
DD contact and the same final NN or DN contact. Here the final flag
$s(x+1)=0$ is essential: following the two strict predecessor paths
cannot identify a later contact with one of the changed rows without
producing a strict cycle or making $x+1$ strict. The deleted strict
graph is a subgraph of the source. The resolved strict graph is obtained
from the source with $e'$ removed by exchanging $p,p+1$ periodically;
it too is acyclic. The induction therefore applies to both children.

Let $T$ be the target required by (R) for $D$, and put $\gamma=1+q$
in the NN case and $\gamma=1$ in the DN case. In $T$, the old edge
$e$ is still a strict corner. Let $U$ unmark this corner of $T$, and
let $W$ delete it. The target for the child $R$ is exactly $U$.
The target for $E$ becomes $W$ after one direct DN move at $p,t$.
We can see both assertions from the rows:

| Diagram | Row $p$ | Row $p+1$ | Row $t$ |
| --- | --- | --- | --- |
| $T$ | $(h,1)$ | $(h,1)$ | $(L-1,1)$ |
| $U$ | $(h,0)$ | $(h,1)$ | $(L-1,1)$ |
| Target of $E$ | $(h-1,1)$ | $(h-1,0)$ | $(L,1)$ |
| $W$ | $(h-1,0)$ | $(h,1)$ | $(L-1,1)$ |

In the DN case every diagram in this table also includes the same changes
at the initial contact: increase $a_{x+1}$ by one and move the strict
head from $x$ to $x+1$. The strict path from $x$ through $p$ to $t$
cannot repeat a residue, and $p+1$ has no outgoing strict edge by the
terminal east gap.
Thus $x$ differs from all three displayed residues. The non-strict row
$x+1$ differs from them because all three are strict in the source.
In the NN case there are no additional changes.

The two shorter-contact relations, and the final direct DN move on the
deletion side, now give

\[
             F_R=\gamma F_U,\qquad F_E=\gamma F_W.
\]

Substitution into (DD1), followed by the corner relation at $e$ in $T$,
gives

\[
       qF_D=\gamma(F_U-F_W)=q\gamma F_T.
\]

We cancel $q$ in the polynomial ring and obtain the required identity in (R). This is an
induction on the number of contacts. In fact $R$ has the same area
sum as $D$ but one fewer strict edge, so its doubled area is one
larger; the outer area induction is not used for this intermediate.
:::

### Separated ND contacts

::: {.proof title="The separated ND relation"}
Suppose the final contact is ND. If the bounce has $k$ intervening
DD contacts, its initial vertex is $x=b^{k+1}(t)$, with $s(x)=0$
and $s(x+1)=1$. We first assume

\[
              b^i(t)\not\equiv x+1\pmod n
              \qquad(0\leq i\leq k).                          \tag{S}
\]

Together with strict acyclicity, this says that the main and parallel
strict contact paths are disjoint. To see the implication, an intersection
propagates backwards along their unique strict predecessors until a main
contact equals $x+1$. Within either path, a repeated residue would give
a strict cycle. Thus their rows can be changed independently.

Put $a=a_x$ and $\ell=a_t$. The zero gap at $x$ gives
$a_{x+1}=a+1$. We have $a\geq1$: if $a=0$, the strict edge into
$x+1$ starts at $x$, whose outgoing strict edge already belongs to the
main path. Strict-successor uniqueness would identify their heads,
contrary to (S). Let $e$ be the strict corner into $x+1$.
We form four auxiliary diagrams:

- $N$ unmarks $e$ in $D$;
- $E$ deletes $e$ from $D$;
- $S$ marks the new corner into $x$ in $E$;
- $J$ deletes that new corner from $E$.

Let $Q$ shorten the terminal strict edge of $D$. Let $N',E',J',R$
be the corresponding terminal shortenings of $N,E,J,S$. Separation
ensures that these terminal changes use different rows from the initial
changes. The two final targets are

| Diagram | Row $x$ | Row $x+1$ | Row $t$ |
| --- | --- | --- | --- |
| $D$ | $(a,0)$ | $(a+1,1)$ | $(\ell,1)$ |
| $Q$ | $(a,0)$ | $(a+1,1)$ | $(\ell-1,1)$ |
| $R$ | $(a,1)$ | $(a,0)$ | $(\ell-1,1)$ |

As before, each entry gives the area and strict flag. All other rows
are unchanged. Condition (S) separates every intervening contact and the
terminal eligibility data from the altered initial rows. The same counted
bounce and terminal eligibility therefore hold in $N,S,J$. The strict
graphs of $N$ and $J$ are subgraphs of the source and remain acyclic.
In $N$ both initial flags are non-strict, with equal
boundaries. In $J$ both contact areas are $a-1$, so their boundaries
again agree. Hence the full NN relation applies to each. The DN target
of $S$ is exactly $Q$. If $S$ is strict-acyclic, the full DN relation
applies. If it has a strict cycle, so does $Q$: exchanging corresponding
vertices of the main and parallel paths transports one strict graph to
the other, including their exterior attachments. Thus both values vanish
in this case, and we still have $F_S=F_Q$.

The four corner relations and these three bounce relations are

\[
\begin{aligned}
 F_N&=F_E+qF_D,       & F_{N'}&=F_{E'}+qF_Q,\\
 F_E&=F_J+qF_S,       & F_{E'}&=F_{J'}+qF_R,\\
 F_N&=(1+q)F_{N'},    & F_J&=(1+q)F_{J'},\\
 F_S&=F_Q.
\end{aligned}                                                   \tag{ND}
\]

Substituting the first two rows into the last two gives

\[
\begin{aligned}
 qF_D
   &=F_N-F_J-qF_S\\
   &=(1+q)(F_{N'}-F_{J'})-qF_Q\\
   &=(1+q)(qF_R+qF_Q)-qF_Q\\
   &=q\bigl(qF_Q+(1+q)F_R\bigr).
\end{aligned}
\]

Cancelling $q$ proves the ND identity in (R).

Both targets preserve the strict-edge count. Their area sums are smaller
by one and two, respectively, so their doubled areas decrease by two
and four. We use outer induction only on these final targets; the
auxiliary relations in (ND) have already been proved by contact-count
induction.
:::

We next treat contacts for which (S) fails.

## Intersecting bounce paths

The preceding recurrences handle disjoint contact paths. On a circle the
paths may meet; the next two reductions handle an intersection at the
terminal vertex and an intersection in the interior, respectively.

### A contact at the terminal vertex

First suppose that $x+1$ has the residue of the terminal vertex $t$.
Write the lower contacts as $p_0,\ldots,p_{r-1}$, in forward strict
order, and put $q_i=p_i+1$ modulo $n$. The strict chain is

\[
 p_0\to\cdots\to p_{r-1}\to q_0\to\cdots\to q_{r-1},
 \qquad q_0=t\pmod n.
\]

The paired vertices are distinct, and $r\geq2$. Exchange each $p_i$
with $q_i$. The target strict chain becomes
$q_0\to\cdots\to q_{r-1}\to p_0\to\cdots\to p_{r-1}$.
We decrease the area at $p_0$ by one and that at $q_0$ by two,
replace the strict corner into $q_0$ by the new corner into $p_0$,
and retain every other strict edge. The initial equal boundaries and
the terminal east gap give a valid diagram $Q$.

::: {.proposition #prop:terminalContact title="An ND contact at the terminal vertex"}
In the terminal ND configuration just described, the diagrams $D,Q$
satisfy, for both values of $F$,

\[
                            F_D=(1+q)F_Q.                       \tag{5}
\]

The strict-edge count is unchanged and the area sum decreases by three.
:::

::: {.proof}
The exceptional non-strict pairs are

\[
 \begin{aligned}
 B&=\{p_iq_i:0\leq i<r\},\\
 C&=\{q_{i-1}p_i:1\leq i<r\},\\
 T&=\{p_{r-1}p_0,q_{r-1}p_0,q_{r-1}q_0\}.
 \end{aligned}
\]

In the source, the $r$ edges of $B$ follow the strict chain, while
$C\cup T$ opposes it. In the target, the $r-1$ edges of $C$ follow
the chain, $B$ opposes it, and the three pairs in $T$ have been removed.
After these pairs are removed, the periodic exchange identifies the
remaining lifted graphs and preserves sink order. Relabeling colorings
and highest reachable vertices therefore identifies the residual sums.
Following edges contribute $1+q$ and opposing edges contribute $1$,
which gives (5). The prescribed changes retain the strict-edge count
and decrease the area by three. Thus the doubled area decreases by six.
:::

### Reversing the columns of a strict chain

At an overlapping ND contact, the two strict paths combine into one
whole strict chain. We write its vertices in chain order as

\[
 w_0\longrightarrow w_1\longrightarrow\cdots
       \longrightarrow w_{r+j-1},\qquad
 w_a+1=w_{a+j}\pmod n\quad(0\leq a<r).                          \tag{6}
\]

Here $w_0$ is the initial main contact, $w_r$ is the terminal vertex,
and $2\leq j<r$. Uniqueness of strict predecessors and successors
propagates the first interior intersection to (6). The ND flag gives a free
initial vertex, and the terminal east gap gives a free final vertex,
so the chain is a whole strict component. The case $j=1$ would make
the terminal strict edge have length one, contrary to $a_t\geq2$.
The case $j=r$ is the terminal contact treated above.

Write $r=dj+s$, where $0\leq s<j$, and form the columns

\[
 C_c=(w_c,w_{c+j},w_{c+2j},\ldots),\qquad
 \ell_c=d+1+\mathbf1_{c<s}\quad(0\leq c<j).
\]

Each column is a consecutive circular interval. The columns are disjoint,
although their subscripts need not be in circular order. Let $H_c$ be
the positive circular distance from the first vertex of $C_{c-1}$ to
the first vertex of $C_c$, with column subscripts modulo $j$.
Then $H_c\geq\ell_{c-1}\geq2$. The areas in $C_c$ are all $H_c$
for $c>0$; in $C_0$ they are $H_0,H_0+1,\ldots,H_0+1$.

Reverse each column, fixing all other vertices, and call this permutation
$\sigma$. Apply it periodically on the integer cover. We obtain a
new diagram $Q$ by transporting the strict edges and setting the areas
as follows:

- if $s=0$, every area in $C_0$ becomes $H_0-1$;
- if $s>0$, every area in $C_0$ becomes $H_0$, and every area in
  $C_s$ decreases by one;
- all other areas remain unchanged.

![Reversal inside consecutive intervals](figures/circular-reversal.svg)

*Figure 3.* We take $r=5$ and $j=2$, so the strict chain is
$w_0\to\cdots\to w_6$. Each row is a consecutive circular interval,
drawn in circular order. The permutation reverses the entries within
each row. The rows need not be adjacent on the circle. Strict edges
in the new diagram are the images of the original chain edges.

::: {.proposition #prop:columnReversal title="Column reversal"}
In the overlapping ND configuration (6), with $2\leq j<r$ and the
whole strict chain and terminal east gap specified above, the prescribed
areas and transported strict edges define a circular
decorated diagram $Q$ with the same number of strict edges as $D$.
Its area sum is smaller by $2d+1$ when $s=0$ and by $2d+2$ otherwise.
Moreover,

\[
 G_D(X;q+1)=\widehat G_D(X;q)
 \quad\Longleftrightarrow\quad
 G_Q(X;q+1)=\widehat G_Q(X;q).
\]
:::

::: {.proof}
At a strict head in $C_c$, $c>0$, the transported edge has length
$H_c+\ell_c-\ell_{c-1}$. At a strict head in $C_0$, its length is
$H_0+\ell_0-\ell_{j-1}-1$. These are the prescribed new areas:
consecutive column lengths agree except at $c=s$ when $s>0$.
Every new area is positive, since $H_c\geq\ell_{c-1}\geq2$.
In particular, when $s=0$, a row with decrement two had old area
$H_0+1\geq3$ and now has area $H_0-1\geq1$. No area increases. In particular the bound $a_i<n$ is preserved.

We check the boundary inequalities at the ends of the columns. Write
$\delta(v)=a_v-a'_v$, so $b'(v)=b(v)+\delta(v)$. Inside a column,
the new area is constant and hence $b'(v+1)-b'(v)=1$.
At a column end with $\delta(v)=0$, the old nonnegative gap suffices.
If that vertex is strict in the target, it was strict in the source
and the old gap is at least one.

The positive decrements at column ends occur in just two places.
When $s=0$, the end of $C_0$ is $w_r=t$, and $\delta(t)=2$.
It is the new source $\sigma(w_0)$ and is not strict. The terminal
east gap gives $b(t+1)-b(t)\geq2$, so the new boundary is
nondecreasing there. When $s>0$, the end of $C_s$ is $t$ and has
decrement one. It remains strict, and the same terminal gap leaves
$b'(t+1)-b'(t)\geq1$. The end of $C_0$ is the new non-strict
source and also has decrement one. It was a strict row, so its old
boundary gap was at least one, which leaves a nonnegative gap.
If the next vertex also has a decrement, the new gap only increases.
These cases prove all cyclic area inequalities and strict-corner conditions.

The transported strict chain has the same number of edges. For $s=0$,
the first row of $C_0$ decreases by one and its other $d$ rows by two,
so the total area decreases by $2d+1$. For $s>0$, the last $d+1$
rows of $C_0$ and all $d+1$ rows of $C_s$ decrease by one. The total
decrease is then $2d+2$.

To compare the two expressions, remove all non-strict edges internal to
the displayed strict component in both diagrams. An internal edge
following the strict-chain order always ascends in a strict coloring.
Its selection does not change the circular HRV map. It therefore
contributes a factor $1+q$ to both expressions. An internal edge
opposing that order never ascends, and its selection creates a cycle;
it contributes no factor.

For the HRV assertion, lift an internal forward edge to $u\to v$.
The strict path from its tail residue to its head residue ends at
$v+kn$ for some $k\geq0$. Hence
$\widetilde H(v)+kn\leq\widetilde H(u)$, and adding $u\to v$
cannot increase any highest reachable value.

The two residual lifted graphs are conjugate by $\sigma$. We give the
boundary check, since a column reversal need not preserve the order of
all vertices.

First consider an exterior head $z$. Its incoming interval cannot start
strictly inside a lifted column. Indeed, let $v$ be an integer lift of
$w_a$, other than the first vertex of its column, so $a\geq j$.
If $w_a$ is not the strict sink, it has strict successor $w_{a+1}$.
Choose the latter's integer lift
$y$ with $b(y)=v$. The preceding row $y-1$ is the lift of
$w_{a+1-j}$, which is also strict. Thus

\[
                    b(y-1)<v=b(y)<b(y+1).
\]

For a row below $y$, monotonicity bounds its boundary by $b(y-1)<v$;
for a row above $y$, it bounds it below by $b(y+1)>v$.
Thus $y$ is the only row with boundary $v$.
It belongs to the displayed component, so no exterior head has this
boundary. If $v$ lifts the strict sink $w_{r+j-1}$, the preceding
integer $v-1$ lifts $w_{r-1}$. Choose the lift of the terminal row $t$
so that $b(t)=v-1$. Its east gap gives $b(t+1)>v$, skipping the
boundary value $v$ entirely. Thus the incoming interval of an exterior head
contains a whole column or misses it. Its area is unchanged, and
reversing the column preserves all its incidences.

For a strict head inside the component, the transported strict edge
identifies its new lower boundary with the reversal of the old lower
boundary. Both lie in the preceding column, and the head stays in its
own column. An exterior vertex therefore crosses neither endpoint of
the incoming interval. The remaining head is the unique non-strict
source $w_0$. Its old lower boundary is the first vertex of the preceding
column, while the boundary of its image $\sigma(w_0)$ is just after
that column. The only changed incidences are again internal. We have
proved the required correspondence for every pair with at least one
exterior endpoint, and the strict edges correspond by construction.

Relabeling colors now identifies the residual coloring sums, including
each normal-edge ascent and the product of vertex variables. The same
edge correspondence gives a bijection on residual selections and
preserves directed paths and acyclicity. A selected sink must be the
terminal vertex of its strict chain, with isolated vertices counted as
one-vertex chains. The moved component has just one such terminal vertex,
which stays in its column; all exterior selected sinks are fixed. No
exterior vertex lies inside that column. Consequently $\sigma$ preserves
the order of integer sink lifts. Every reachable vertex extends to a sink,
so the correspondence transports highest reachable vertices and preserves
their fibre sizes. It identifies the residual HRV sums as well.

Let $f_D,f_Q$ be the numbers of deleted edges following strict-chain
order in the respective diagrams. There are common residual expressions
$C,E$ with

\[
 \begin{aligned}
 G_D(X;q+1)&=(1+q)^{f_D}C,&\widehat G_D(X;q)&=(1+q)^{f_D}E,\\
 G_Q(X;q+1)&=(1+q)^{f_Q}C,&\widehat G_Q(X;q)&=(1+q)^{f_Q}E.
 \end{aligned}
\]

The equality for $Q$ gives $C=E$ by cancellation of $(1+q)^{f_Q}$,
and hence gives the equality for $D$. Conversely, cancellation of
$(1+q)^{f_D}$ gives the reverse implication.
:::

## Completing the induction

::: {.proof title="Proof of Theorem \ref{thm:circularExpansion}"}
We use the lexicographic induction (measure), treating strict cycles as
zero cases. We now check that the previously proved reductions cover
every remaining diagram.

A non-strict corner gives the first identity in (R); deletion decreases $\mu$ by two,
and strict marking decreases it by one. We may therefore suppose
all corners are strict. If no non-strict edge remains, the chain
product proves the theorem.

Otherwise some area is at least two. A positive constant area sequence
with every corner strict would give a strict cycle. An exit from a
plateau of maximal area therefore supplies an eligible terminal row.
At a lower contact with a positive east gap, restart there. At a DD
contact continue backwards. Every step follows an actual strict edge
backwards and decreases the number of strict ancestors. The search
therefore ends at NN, DN or ND.

For NN, (R) decreases $\mu$ by two. For DN it preserves $\mu$ and
decreases $\nu$: the exchange conjugates the strict paths and preserves
ancestor depths, while the initial edge length increases by one and
the terminal edge length decreases by one. Thus the change in $\nu$ is
$d(p_0)-d(t)<0$, where $p_0$ and $t$ are the initial and terminal
vertices on the longer strict path. For separated ND, the targets in
(R) decrease $\mu$ by two and four. An ND contact at the terminal vertex
uses (5), decreasing $\mu$ by six. For an interior intersection, column
reversal strictly decreases $\mu$, and the residual comparison transfers
the identity from the smaller diagram. These cases prove the theorem.
:::
