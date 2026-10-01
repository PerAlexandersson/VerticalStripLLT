# The circular elementary expansion

We first prove the elementary expansion for a circular diagram. The
highest reachable vertex is defined on its integer cover. This allows the
local relations to pass through the chosen cut of the circle. When two
contact paths meet, we reverse consecutive intervals in their common
strict chain and reduce the area.

## Circular diagrams and highest reachable vertices

Let $n\geq1$, and let $(a_0,\ldots,a_{n-1})$ satisfy
$0\leq a_i<n$ and $a_{i+1}\leq a_i+1$, with subscripts modulo $n$.
We extend the sequence periodically and put $b(i)\coloneqq i-a_i$.
The natural edges in row $i$ are

\[
                 b(i)\longrightarrow i,\quad\ldots,\quad i-1\longrightarrow i.
\]

We identify integer translates by $n$. A natural edge retains its positive
lift, of length less than $n$. In particular, opposite edges between two
residues are distinct. The first edge in row $i$ is a corner when
$a_i>0$ and $b(i+1)>b(i)$. We may mark any subset $S$ of the corners
strict. We denote the resulting decorated diagram by $D$.

For a finite alphabet $X=(x_1,\ldots,x_m)$, define

\[
 G_D(X;q)\coloneqq
 \sum_{\substack{\kappa:\mathbb Z/n\mathbb Z\to\{1,\ldots,m\}\\
       uv\in S\Rightarrow\kappa(u)<\kappa(v)}}
 q^{\#\{uv\notin S:\kappa(u)<\kappa(v)\}}
 \prod_u x_{\kappa(u)}.
\]

A selected state $A$ contains all strict edges and any subset of the
remaining natural edges. We call $A$ admissible when its directed graph
on residues is acyclic. For an integer $u$, let

\[
 \widetilde H_A(u)\coloneqq
 \max\{v\in\mathbb Z:v\text{ is reachable from }u\text{ in the lift of }A\}.
\]

We allow paths of length zero. A path cannot repeat a residue, so this
maximum exists. Moreover, $\widetilde H_A(u+n)=\widetilde H_A(u)+n$.
Its residue defines a map $H_A$ on the vertices of the circular diagram.
Let $\lambda(A)$ be the partition of the sizes of its nonempty fibres,
and put

\[
 \widehat G_D(X;q)\coloneqq
 \sum_{A\text{ admissible}}q^{|A\setminus S|}e_{\lambda(A)}(X).
\]

For example, take $(a_0,a_1,a_2)=(1,1,1)$ with no strict corners.
The natural edges form the directed cycle $0\to1\to2\to0$.
The selected path $2\to0\to1$ lifts to $2\to3\to4$.
All three vertices therefore have highest reachable residue $1$.
The empty selection, the three single edges and the three two-edge
paths give

\[
 \widehat G_D(X;q)=e_1(X)^3+3q e_2(X)e_1(X)+3q^2e_3(X).
\]

**Circular expansion theorem.** For every circular decorated diagram,

\[
                 G_D(X;q+1)=\widehat G_D(X;q).
\]

Thus the shifted polynomial has nonnegative coefficients in the elementary
basis. The identity holds for every finite alphabet and hence
coefficientwise in infinitely many variables.

## The local reductions

Throughout the proof, $F_D$ denotes either of the two expressions in the
theorem. If a non-strict corner is deleted or marked strict, write the
result as $D^-$ or $D^{\mathrm s}$, respectively. We have

\[
                   F_D=F_{D^-}+qF_{D^{\mathrm s}}.                 \tag{1}
\]

For colorings, this is the expansion of the corner weight
$1+q\,\mathbf1_{\kappa(u)<\kappa(v)}$. For selected states, we split
according to whether the corner is selected. In the selected term its
strict marking preserves reachability and removes one factor $q$.

Every vertex has at most one incoming and one outgoing strict edge.
Consequently the strict graph consists of chains and cycles. A strict
cycle makes both expressions zero. If every natural edge is strict and
there is no cycle, both expressions are the product of $e_{|B|}(X)$
over the strict chains, including isolated vertices.

Write $s(i)$ for the strict flag in row $i$ and
$g(i)\coloneqq b(i+1)-b(i)-s(i)$ for the number of east steps after
that row. A bounce starts at a strict row $t$ with $a_t\geq2$ and
$g(t)>0$. Its first lower contact is $x=b(t)$. At a contact with
$g(x)=0$, the flags $s(x),s(x+1)$ specify NN, DN, ND or DD.
A DD contact continues the bounce backwards along the strict path.

The NN relation shortens the original terminal strict edge by one and
has coefficient $1+q$. The DN relation additionally moves the initial
strict head from $x$ to $x+1$ and has coefficient $1$. In path notation,

\[
 \begin{aligned}
 F_{U\mathrm{nn}V\mathrm{de}W}
   &=(1+q)F_{U\mathrm{nn}V\mathrm{ed}W},\\
 F_{U\mathrm{dn}V\mathrm{de}W}
   &=F_{U\mathrm{nd}V\mathrm{ed}W}.
 \end{aligned}                                                   \tag{2}
\]

Here the displayed steps specify the contact and terminal changes in the
integer lift; all periodic exterior data remain in place.

![The direct NN and DN relations as weighted sums](figures/circular-direct-relations.svg)

*Figure 1.* These are the direct contacts in (2), with $y=p+1$.
Each picture sums over
its optional natural edges with weight $q^{|A\setminus S|}$. The
labels denote integer lifts; the periodic exterior is summed over and
satisfies the contact conditions. The equations hold for the corresponding
weighted sums of strict-coloring values and of admissible HRV values.
We prove these two identities separately below.

### Boundary symmetry and the coloring relations

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

### The four selected triangles

For the orientation calculation, consider a lifted triangle $P<Y<T$ with
$P\to T$ mandatory. With all other selected edges fixed, let $M_U$
be the HRV elementary monomial after adding
$U\subseteq\{P\to Y,Y\to T\}$, taking value zero for a cycle.
The four selections satisfy

\[
 M_{\{P\to Y\}}+M_{\{Y\to T\}}
       =M_\varnothing+M_{\{P\to Y,Y\to T\}}.                     \tag{3}
\]

We first note that adding $u\to v$ preserves the entire lifted HRV
map whenever $\widetilde H(v)\leq\widetilde H(u)$. The old HRV
function is nonincreasing along every old edge and along every periodic
copy of the added edge. Hence a new path starting at $z$ still ends at
or below $\widetilde H(z)$, and the old maximizing path is still
available. This also proves acyclicity: a directed cycle on residues
could be repeated in the lift to produce arbitrarily large endpoints.

If the bottom selection is cyclic, all four terms are zero. Otherwise
let $H$ be its lifted HRV map; the mandatory edge gives $H(T)\leq H(P)$.
We distinguish two cases.

If $H(Y)\leq H(P)$, adding $P\to Y$ changes nothing. If adding
$Y\to T$ creates a cycle, the two terms containing that edge both
vanish. Otherwise a new path from $Y$ either avoids the added edge or
starts with it: it cannot first return to another lift of $Y$, since
that would give a cycle on residues. Its greatest endpoint is therefore
at most $\max(H(Y),H(T))\leq H(P)$. Thus $P\to Y$ is ineffective
after adding $Y\to T$ as well. This pairs the bottom with the first
middle term and the other middle term with the top.

If $H(P)<H(Y)$, the ineffective bottom edge is $Y\to T$. After
adding $P\to Y$, either both terms containing it vanish, or the
highest vertex reachable from $T$ stays $H(T)$. Indeed, a path from
$T$ cannot reach a lift of $P$, since the mandatory edge back to the
residue of $T$ would make a cycle. The HRV at $Y$ can only increase,
so $Y\to T$ remains ineffective. This gives the other pairing and
proves (3), including all cyclic cases.

After inserting weights, (3) becomes

\[
 M_\varnothing+q(M_{\{P\to Y\}}+M_{\{Y\to T\}})
       +q^2M_{\{P\to Y,Y\to T\}}
 =(1+q)(M_\varnothing+qM_{\{P\to Y,Y\to T\}}).
\]

The bottom terms in (2) correspond under the periodic exchange of the
contact vertices; the top terms have the same transitive closure.
The exchange preserves order on sinks: its only inverted pairs are
$x+kn,x+1+kn$, and the first vertex has a mandatory outgoing edge.
Every reachable vertex extends to a sink. Thus the exchange transports
the highest reachable map and preserves its fibre sizes.

### Removing intervening DD contacts

We prove (2) by induction on the number of intervening DD contacts,
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

Let $T$ be the target required by (2) for $D$, and put $\gamma=1+q$
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

We cancel $q$ in the polynomial ring and obtain (2). This is an
induction on the number of contacts. In fact $R$ has the same area
sum as $D$ but one fewer strict edge, so its doubled area is one
larger; the outer area induction is not used for this intermediate.

### Separated ND contacts

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

Put $A=a_x$ and $L=a_t$. The zero gap at $x$ gives
$a_{x+1}=A+1$. We have $A\geq1$: if $A=0$, the strict edge into
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
| $D$ | $(A,0)$ | $(A+1,1)$ | $(L,1)$ |
| $Q$ | $(A,0)$ | $(A+1,1)$ | $(L-1,1)$ |
| $R$ | $(A,1)$ | $(A,0)$ | $(L-1,1)$ |

As before, each entry gives the area and strict flag. All other rows
are unchanged. Condition (S) separates every intervening contact and the
terminal eligibility data from the altered initial rows. The same counted
bounce and terminal eligibility therefore hold in $N,S,J$. The strict
graphs of $N$ and $J$ are subgraphs of the source and remain acyclic.
In $N$ both initial flags are non-strict, with equal
boundaries. In $J$ both contact areas are $A-1$, so their boundaries
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

Cancelling $q$ proves

\[
                        F_D=qF_Q+(1+q)F_R.                       \tag{4}
\]

Both targets preserve the strict-edge count. Their area sums are smaller
by one and two, respectively, so their doubled areas decrease by two
and four. We use outer induction only on these final targets; the
auxiliary relations in (ND) have already been proved by contact-count
induction. We next treat contacts for which (S) fails.

## A contact at the terminal vertex

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
which gives

\[
                            F_D=(1+q)F_Q.                       \tag{5}
\]

The strict-edge count is unchanged and the area decreases by three.
Thus this case reduces the doubled area by six.

## Reversing the columns of a strict chain

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

At a strict head in $C_c$, $c>0$, the transported edge has length
$H_c+\ell_c-\ell_{c-1}$. At a strict head in $C_0$, its length is
$H_0+\ell_0-\ell_{j-1}-1$. These are the prescribed new areas:
consecutive column lengths agree except at $c=s$ when $s>0$.
Every new area is positive, since $H_c\geq\ell_{c-1}\geq2$,
and no area increases. In particular the bound $a_i<n$ is preserved.

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

Relabeling colors now identifies the residual coloring sums. For the
orientation sums, every selected sink is a strict sink. The moved
component has just one strict sink, which stays in its column; all
other strict sinks are fixed. Consequently $\sigma$ preserves the
order of integer sink lifts and transports highest reachable vertices.
It identifies the residual HRV sums as well.

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
and hence gives the equality for $D$.

## Completing the induction

Set

\[
 A_2(D)\coloneqq2\sum_i a_i-|S|,
 \qquad
 J(D)\coloneqq\sum_{e\in S}d(\operatorname{head}(e))\ell(e),
\]

where $\ell(e)$ is the positive circular length of $e$ and $d(v)$
is the number of proper strict ancestors of $v$. We induct lexicographically
on $(A_2(D),J(D))$, treating strict cycles as zero cases.

A non-strict corner gives (1); deletion decreases $A_2$ by two,
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

For NN, (2) decreases $A_2$ by two. For DN it preserves $A_2$ and
decreases $J$: the exchange conjugates the strict paths and preserves
ancestor depths, while the initial edge length increases by one and
the terminal edge length decreases by one. Thus the change in $J$ is
$d(p_0)-d(t)<0$, where $p_0$ and $t$ are the initial and terminal
vertices on the longer strict path. For separated ND, the targets in
(4) decrease $A_2$ by two and four. An ND contact at the terminal vertex
uses (5), decreasing $A_2$ by six. For an interior intersection, column
reversal strictly decreases $A_2$, and the residual comparison transfers
the identity from the smaller diagram. These cases prove the theorem.
