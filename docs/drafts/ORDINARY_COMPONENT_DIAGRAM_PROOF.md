# Elementary expansions of ordinary flip components

We prove the component expansion by applying the local diagram relations to
whole components. The main step is to connect the states in which every
maximal corner is a cover. We then complete such a component to an entire
edge layer, apply the local relation, and remove the additional components by
induction. An endpoint attachment extends this construction to diagrams with
articulations.

## Selected diagrams and their two values

Let $G$ be an ordinary decorated natural diagram on $0,\ldots,n-1$.
Its area sequence satisfies $a_0=0$, $0\leq a_j\leq j$ and
$a_{j+1}\leq a_j+1$. The natural edges ending at $j$ are $ij$ with
$j-a_j\leq i<j$. A natural corner is an edge whose interval is contained in no larger
natural interval. We may mark any subset of these corners strict.
A state $A$ is a selection of natural edges containing every strict edge.
All edges point from the smaller vertex to the larger vertex. For a finite
alphabet $X=(x_1,\ldots,x_m)$, we put

\[
 K(A;X)\coloneqq
 \sum_{\substack{\kappa:\{0,\ldots,n-1\}\to\{1,\ldots,m\}\\
                    uv\in A\Rightarrow\kappa(u)<\kappa(v)}}
 \prod_{u=0}^{n-1}x_{\kappa(u)}.
\]

Let $H_A(u)$ be the greatest vertex reachable from $u$, allowing the path
of length zero. Write $\lambda(A)$ for the partition of the nonempty fibre
sizes of $H_A$, and put $E(A;X)\coloneqq e_{\lambda(A)}(X)$.
Equivalently, we obtain $E(A;X)$ by replacing every fibre by its increasing
chain and enumerating its strict colorings. We use this chain description
when a vertex color is fixed.

A selected edge $uv$ is a cover if there is no selected path from $u$
to $v$ with an intermediate vertex. For $i<j<k$, a flip exchanges
$ij$ and $jk$, retaining $ik$ and every other selected edge. We require
$ij,ik$ to be covers before the exchange and $ik,jk$ to be covers
afterwards. Both exchanged edges are non-strict. The flip components
are the connected components under these moves.

A flip preserves the number of selected edges and the selected weak
blocks. In fact, the retained long edge joins $i$ to $k$, and either
short edge joins $j$ to that same block. A maximal natural corner
cannot be exchanged as a short edge, since it would then lie properly
inside the retained long edge. Its selected status is therefore
constant on each whole component.

For a whole flip component $C$, we sum either value over its states:
$K(C;X)=\sum_{A\in C}K(A;X)$ and
$E(C;X)=\sum_{A\in C}E(A;X)$.

**Theorem.** For every ordinary decorated natural diagram and every whole
flip component $C$, we have

\[
                     K(C;X)=E(C;X).
\]

Expanding each normal-edge weight after the shift gives

\[
 \operatorname{LLT}_G(X;q+1)
     =\sum_A q^{|A\setminus S|}K(A;X),
\]

where $S$ is the original strict set and $A$ runs over all selected states.
The number $k(C)$ of selected normal edges is constant on a flip component.
Consequently its contribution to the LLT polynomial after the shift
$q\mapsto q+1$ is

\[
                q^{k(C)}\sum_{A\in C}e_{\lambda(A)}(X).
\]

## Local moves and the diamond identity

We use cell diagrams to denote sums over selected states satisfying the
displayed restrictions. The diagonal lists the ordered vertices. A blank
cell is an optional natural edge, $1$ requires a selected normal edge,
$0$ requires it absent, and a cross means there is no natural edge.
An arrow denotes a strict edge. Underlining a selected entry additionally
requires a cover in the full selected relation. Conditions below a diagram
restrict the entire sum, for example to $|A|=s$.
All cells in this section are unweighted. The surrounding statement fixes
$V=K$ or $V=E$ and specifies whether the exterior selection is fixed or
summed. With every selection fixed, the diagram gives one state value.

We next use a relation between values of states. Fix a forward
selected relation $B$ containing $ik$ and omitting $ij,jk$, and put

\[
 B_{00}=B,\qquad B_{10}=B\cup\{ij\},\qquad
 B_{01}=B\cup\{jk\},\qquad B_{11}=B\cup\{ij,jk\}.
\]

**Diamond lemma.** For $V=K,E$, we have

\[
                  V(B_{10})+V(B_{01})=V(B_{00})+V(B_{11}).
                  \tag{D}
\]

The identity also holds with the color of any specified vertex fixed.
There are no cover hypotheses, and the exterior selected edges are arbitrary.

![Four selected states in the diamond identity](figures/ordinary-diamond.svg)

*Figure 1.* Each off-diagonal cell records whether the corresponding
natural edge is selected. The long edge $ik$ is retained in all four
states. Equation (D) holds even when the two middle states are not
joined by a flip.

*Proof.* For a coloring strict on $B$, write its colors at $i,j,k$ as
$a,b,c$. Since $a<c$, we have

\[
             \mathbf1_{a<b}+\mathbf1_{b<c}
                 =1+\mathbf1_{a<b<c}.
\]

Multiplication by the coloring monomial and summation prove the $K$
identity, including any prescribed vertex color.

For $E$, we prove the stronger multiset identity

\[
                 \{H_{B_{10}},H_{B_{01}}\}
                    =\{H_{B_{00}},H_{B_{11}}\}.
\]

Adding $uv$ leaves the entire highest reachable map unchanged whenever
$H_B(u)\geq H_B(v)$. A new path using $uv$ can reach only an old
descendant of $v$, and every old predecessor of $u$ already reaches a
vertex at least as large as $H_B(v)$.

If $H_B(j)\geq H_B(k)$, adding $jk$ is therefore ineffective in $B$.
It is also ineffective in $B\cup\{ij\}$, since the earlier edge $ij$
changes no path starting at $j$ or $k$. Thus
$H_{B_{01}}=H_{B_{00}}$ and $H_{B_{11}}=H_{B_{10}}$.
If $H_B(j)<H_B(k)$, the retained $ik$ gives
$H_B(i)\geq H_B(k)>H_B(j)$. Adding $ij$ is ineffective both before
and after $jk$ is added. This gives the other pairing. Equal maps have
equal canonical fibre chains, proving the marked $E$ identity as well.

We will also delete a redundant selected edge when a selected alternate
path between its endpoints remains. This preserves the transitive closure,
so it preserves the coloring constraints, the highest reachable map,
and their marked values.

## Three reductions to smaller components

We write $M$ for the maximal natural corners. The following reductions
apply to whole components; their coefficients are the same for $K$ and $E$.

**Absent corner.** Suppose a state of a component $C$ omits $f\in M$.
Every state of $C$ then omits $f$. Delete $f$ from the natural diagram.
The selected relations and their cover tests are unchanged, and no flip
of $C$ can use the absent edge as its retained long. Conversely, every
flip of the smaller diagram lifts. Thus $C$ is exactly one whole
component of a diagram with one fewer natural edge.

**Disconnected selected graph.** Suppose the natural graph is connected
but the selected weak graph of $C$ is disconnected. Its weak blocks are
constant throughout $C$. Put these blocks in consecutive intervals,
preserving the vertex order inside each block, and keep the induced
natural diagram on each block. At least one natural edge between blocks
is lost, so natural area strictly decreases.

Every selected edge and every flip stays inside a weak block. Paths
between vertices of that block stay there as well, so restriction and
relabeling preserve all cover tests. The inverse relabeling has the same
property. Consequently the resulting states form one whole component.
Color relabeling preserves $K$. Since the order inside every block is
preserved, the sizes of all highest reachable fibres are unchanged, so
$E$ is preserved too. When the greatest vertex has a fixed color, we
put its weak block last. The relabeling then fixes that vertex.

**No simultaneous corner covers.** Suppose every corner in $M$ is
selected throughout $C$, but no state has all of them covering
simultaneously. First mark all corners in $M$ strict. This preserves
the whole component: corners cannot be exchanged, and their strict
marking changes neither the full selected relations nor their cover tests.

For $T\subseteq M$, delete the corners in $T$. We identify states in
these diagrams by their unchanged normal selections. The smaller flip
graph is a spanning subgraph of the original one: exactly the flips
retaining a deleted corner as their long edge are removed. Indeed, an
alternate path testing another natural edge lies inside its interval;
it cannot use a distinct maximal interval. Thus the image of $C$ is a
disjoint union of whole deletion components. Denote this partition by
$\mathcal P_T(C)$.

Fix a state $A\in C$ and choose one redundant corner $f\in M$.
Its alternate path lies strictly inside its interval and uses no other
maximal corner. It survives deletion of every subset of $M\setminus\{f\}$.
For $V=K,E$, pair subsets $T$ and $T\cup\{f\}$ to obtain

\[
                  \sum_{T\subseteq M}(-1)^{|T|}V(A\setminus T)=0.
\]

The redundant corner may depend on $A$. Summing over $C$ and isolating
the empty deletion gives

\[
 V(C)=\sum_{\varnothing\ne T\subseteq M}(-1)^{|T|+1}
                   \sum_{C'\in\mathcal P_T(C)}V(C').              \tag{C}
\]

Each component on the right belongs to a diagram with strictly fewer
natural edges. The cancellation preserves the full highest reachable
map and all coloring constraints, so (C) also holds with a fixed vertex
color. We keep this identity unweighted: the original normal-edge exponent
is restored only after the component identity, since remarking changes it.

We also normalize the ambient diagram using the absent-corner reduction.
Let $H$ consist of every natural interval contained in some selected
interval. A flip exchanges shorts inside a retained long, so $H$ is
constant on $C$. If the ambient diagram has an edge outside $H$, choose
a maximal natural interval containing it. This interval is also outside
$H$, hence is an absent corner. Delete it and repeat. The process ends
at the valid natural diagram $H$, preserving the whole component at
every step. Every maximal interval of $H$ is selected, since an interval
generating it must equal it by maximality. We may therefore mark all
its corners strict. Proper deletion reduces natural area; changing the
strict markings is only a new representation of the same selected states.

## Connecting the states with corner covers

A common-cover state is one in which every maximal natural corner is a
cover. Let $M$ be the set of these corners. They form disjoint
directed chains. We write $r(u)$ for the last vertex in the chain containing
$u$. An anchor consists of all edges in $M$ and any additional natural
edges $uv$ satisfying $r(u)<r(v)$. Denote the union of all these allowed
edges by $A^*(G)$. The preparation lemma connects every state in which all
corners are covers to an anchor. Its paths retain the corners; a corner
may become redundant at an intermediate state.

We first treat the case in which the first two maximal corners are
$0a$ and $1b$, with $1<a<b$. Let $G'$ be the induced diagram on
$1,\ldots,n-1$. Deleting zero removes the corner $0a$. Every edge left
from its clique lies in the clique $[1,b]$, so no new maximal corner appears.
The other corner chains lose no successors, and therefore retain their
terminal vertices.

It follows that

\[
 A^*(G)=\{0a\}\,\sqcup\,A^*(G')\,\sqcup\,\{0v:v\in J\},
 \qquad J\coloneqq\{v:0<v<a,\ r(a)<r(v)\}.
 \tag{1}
\]

Indeed, a good edge at zero is either $0a$ or an edge $0v$ with
$v<a$ and $r(0)=r(a)<r(v)$. Every other edge lies in the core, where
both its terminal labels and its corner status are unchanged.

For $v\in J$, let $vh_v$ be its corner successor. Such a successor
exists: $r(v)>r(a)\geq a>v$. Moreover, $h_v>a$, since a maximal corner
starting between zero and $a$ cannot end within $[0,a]$. The edge
$d_v\coloneqq ah_v$ is a normal good edge of $G'$. The crossing slide
exchanges $0v$ and $d_v$, with the corners $0a$ and $vh_v$ retained.

![The initial crossing slide](figures/initial-crossing.svg)

*Figure 2.* The diagonal lists the ordered vertices $0<v<a<h=h_v$.
The cell in column $u$ and row $w$ represents the edge $uw$.
Arrows denote the two retained corner covers, and $1$ and $0$ denote
selected and absent normal edges. The edge $va$ is natural because it
lies in $[0,a]$, but an anchor does not select it since $r(v)>r(a)$.
The displayed change is a path of flips; every
other edge, including edges on vertices omitted from the figure, is
restored at its endpoint.

**Initial-vertex lemma.** Suppose that connected common-cover states of
each size in $G'$ belong to one flip component. Suppose also that
$A^*(G')\setminus\{d_v\}$ is connected for every $v\in J$.
Then connected common-cover states of each size in $G$ belong to one
flip component.

*Proof.* We prepare the two states to anchors. We first make each selected
core connected, then change its extra edges at zero.

Let $A$ be a connected anchor whose selected core is disconnected, and
let $B$ be the core component containing $a$. Some selected edge $0v$
enters a different core component. Otherwise all selected neighbors of
zero would lie in $B$, contradicting connectedness of $A$. The edge
$0v$ is an extra, since $0a$ enters $B$. The selected corner $vh_v$
puts $h_v$ in the same core component as $v$. Hence $ah_v$ is absent.
We apply the crossing slide in Figure 2. The core gains $ah_v$ and loses
no edge, while the initial row loses $0v$. Repeating this operation
terminates because the number of selected initial extras decreases.

Now fix the set $S\subseteq J$ of selected extras and the total selected
size $s$. The core has size $t=s-1-|S|$. Any two connected core anchors
of this size are connected by the hypothesis on $G'$. Every core flip
lifts with $0a$ and all edges $0v$, $v\in S$, fixed: a forward path
between positive vertices cannot pass through zero. At the final core
anchor all selected edges are again good for $G$, so the endpoint is
an ambient anchor. Thus the anchors with fixed $S$ and connected core
are connected.

Put $r=n-2$ and $m=|A^*(G')|$. The corner edges of the core form a
forest. In a connected good-edge graph we extend this forest to a
spanning tree, then add edges. Consequently a connected core anchor
exists at every size $r,\ldots,m$. The possible sets $S$ are exactly

\[
 S\subseteq J,\qquad
 \max(0,s-1-m)\leq |S|\leq\min(|J|,s-1-r).
 \tag{2}
\]

Suppose that $v\in S$ and both $S$ and $S\setminus\{v\}$ satisfy (2).
Their core sizes are $t$ and $t+1$, so $r\leq t\leq m-1$.
By hypothesis the graph $A^*(G')\setminus\{d_v\}$ is connected. Its
corner forest extends to a spanning tree, and we add good edges to
obtain a connected core anchor of size $t$ omitting $d_v$. We lift
this anchor with exactly the initial extras $S$. The crossing slide
replaces $0v$ by $d_v$. Its endpoint has connected core of size $t+1$
and initial extras $S\setminus\{v\}$. The fixed-$S$ paths on either
side connect any two anchors in these neighboring cases.

The sets in (2) are connected by these insertions and deletions. To see
this, first adjust cardinality within the permitted interval. To exchange
an unwanted element for a wanted one at a fixed size, delete first if
the size is above the lower bound, and insert first otherwise. The only
possible obstruction would be an intermediate band of just one size.
If $J$ is nonempty, the removable-edge hypothesis gives $m\geq r+1$,
which excludes this obstruction: a one-size band is then either
$\{\varnothing\}$ or $\{J\}$. If $J$ is empty there is only one set.
We concatenate these paths and reverse the preparation of the target.

**Common-cover uniqueness.** If the ordinary natural graph is connected
and has no articulation, then connected common-cover states of the same
total selected size belong to one flip component.

*Proof.* We induct on the number of vertices. We use the complete-diagram
and two-corner-chain path lemmas for the base cases. Otherwise write the
first two corners as $0a$ and $bc$. Consecutive maximal cliques overlap
in at least two vertices, so $0<b<a<c$.

If $b>1$, the reflected last-clique lemma reduces to the induced core
on $\{0,b,b+1,\ldots,n-1\}$. The first retained clique and its successor
still overlap in at least two vertices, and all later overlaps are
unchanged. The core has fewer vertices and no articulation, so induction
supplies its required path theorem.

If $b=1$, deleting zero removes just $0a$. The remaining graph has fewer
vertices and no articulation, and the number of corner chains is unchanged.
It has at least three chains outside the base cases. Contracting these
chains in its good-edge graph gives the connected quotient without
articulation of the corner-chain lemma. A connected graph without
articulation on at least three vertices has no bridge. Removing one copy
of a good edge therefore leaves the good-edge graph connected: if it
were the only copy of its class, we lift a path around that quotient
edge, using corner chains to join consecutive copies. This verifies
the removable-edge hypothesis of the initial-vertex lemma.

An initial path may be adjoined to this graph. We remove its pendant
vertices one at a time. Each has just one natural edge, which must be
selected in a connected state, and every core flip lifts. Reversing
these restrictions gives the same uniqueness statement for the graph
with its initial path.

## Completing one component to an edge layer

Let $\mathcal L_s(D)$ denote all states with exactly $s$ selected edges,
including the strict edges. Each layer is a disjoint union of whole
components. We first apply the diagram relations to the entire layer,
then use the smaller-component reductions to isolate the required component.

At an eligible NN contact, write $w<x=w+1<z$, with $wz$ strict.
The target $R$ deletes $wz$ and marks $xz$ strict. An exterior selection
$Q$ contains the required strict exterior edges and is disjoint from all
displayed local edges. For a fixed such $Q$, the source states are

\[
 L_{ij}(Q)=Q\cup\{wz\}\cup i\{wx\}\cup j\{xz\},
 \qquad i,j\in\{0,1\},
\]

where $i\{e\}$ means $\varnothing$ or $\{e\}$ according as $i=0$
or $i=1$. The target states are
$R_i(Q)=Q\cup\{xz\}\cup i\{wx\}$.
The eligible contact geometry makes the adjacent transposition
$\sigma=(w\ x)$ an involution of the exterior selections. It preserves
their cardinality and the required exterior strict edges. The bottom
and top comparisons are

\[
 V(L_{00}(Q))=V(R_0(\sigma Q)),\qquad
 V(L_{11}(Q))=V(R_1(Q)),\qquad V=K,E.
\]

The first is relabeling. The second deletes the redundant $wz$ from
the selected path $w\to x\to z$. For $E$, the relabeling preserves
sink order: the only exchanged consecutive pair contains $w$, which
has a selected outgoing edge. It therefore preserves the HRV fibre sizes.
The diamond supplies the sum of the two middle values.

For clarity, count the selected exterior edges by $t=|Q|$. The source
sizes are $t+1,t+2,t+2,t+3$, whereas the target sizes are $t+1,t+2$.
Write $B_t$ and $C_t$ for the sums of the target bottom and top values
over exterior selections of size $t$, taking these sums to be zero
when $t<0$. Reindexing the bottom sum by $\sigma$, we obtain

\[
 \begin{aligned}
 V(\mathcal L_s(D))
   &= B_{s-1}+B_{s-2}+C_{s-2}+C_{s-3},\\
 V(\mathcal L_s(R))&=B_{s-1}+C_{s-2}.
 \end{aligned}
\]

Consequently

\[
 V(\mathcal L_s(D))
   =V(\mathcal L_s(R))+V(\mathcal L_{s-1}(R)).          \tag{LNN}
\]

For a DN contact, let $u<w<x=w+1<z$. The source strict edges are
$uw,wz$, and the target strict edges are $ux,xz$. Again $Q$ is disjoint
from all displayed local edges. The eligible geometry makes $Q\mapsto\sigma Q$
a bijection on the permitted exterior selections, retaining the required
strict exterior edges. We use the states

\[
 \begin{aligned}
 L_{ij}(Q)&=Q\cup\{uw,wz\}\cup i\{wx\}\cup j\{xz\},\\
 R_{ij}(Q)&=Q\cup\{ux,xz\}\cup i\{uw\}\cup j\{wx\}.
 \end{aligned}
\]

Both sets of four states have sizes $t+2,t+3,t+3,t+4$.
The bottom comparison again exchanges $w,x$ in the exterior selection.
The top states have the same transitive closure: both contain the chain
$u\to w\to x\to z$, and their additional edges $wz$ or $ux$ are
redundant. Apply the diamond to the source triangle $w,x,z$ and the
target triangle $u,w,x$. The paired middle sums agree after summing over
all exterior selections of each size. Thus

\[
                    V(\mathcal L_s(D))=V(\mathcal L_s(R)).       \tag{LDN}
\]

![NN and DN as sums over restricted selections](figures/layer-relations.svg)

*Figure 3.* The blank cells and permitted exterior edges are summed over.
Arrows require strict edges, and crosses remove natural edges. The condition
$|A|=s$ counts all selected edges, including strict edges. Each diagram is
an entire layer sum for $V=K$ or $V=E$ at an eligible contact.

Now suppose $D$ has the common-cover uniqueness proved above, including
the case of an initial path followed by a graph without articulation.
Let $C$ be a connected component in layer $s$ containing a state in
which every maximal corner is a cover. Every other component $C'$ in
that layer has one of the three smaller reductions: it omits a corner,
has disconnected selected graph, or has no simultaneous-cover witness.
In the last case we first mark all selected maximal corners strict and
apply (C). Let $B_V(C')$ denote the resulting signed sum of whole
smaller components.

We add all these other source components to $C$, use (LNN) or (LDN),
and subtract their reductions. This gives

\[
 \begin{aligned}
 \mathrm{NN}:\quad V(C)
  &=V(\mathcal L_s(R))+V(\mathcal L_{s-1}(R))
      -\sum_{C'\ne C}B_V(C'),\\
 \mathrm{DN}:\quad V(C)
  &=V(\mathcal L_s(R))-\sum_{C'\ne C}B_V(C').
 \end{aligned}                                                   \tag{L}
\]

Each target layer is itself partitioned into its whole components.
The source corrections and these target components give exactly the
same integer coefficients for $K$ and $E$. No other source component's
expansion was used: each correction was obtained directly from one of
the three reductions. In NN the target has one fewer natural edge.
In forward DN its area is unchanged, but its area moment decreases.
We verify the latter decrease when choosing the contact below.

## Keeping the right endpoint through a recurrence

Let $c$ be the largest vertex of a prefix. Fix its color $\beta$.
Write $K(A)[\beta]$ for the coloring sum with this condition, including
the weight $x_\beta$. Define $E(A)[\beta]$ using the increasing chains
of the actual HRV fibres with the same condition. If the fibre of $c$
has size $p$, then

\[
 E(A)[\beta]=x_\beta e_{p-1}(X_{<\beta})
                  \prod_{F\ne H_A^{-1}(c)}e_{|F|}(X).
 \tag{3}
\]

The local diamond identities hold with this color fixed. On the coloring
side they hold for each coloring; on the HRV side they preserve the
multiset of full HRV maps. Redundant-edge changes preserve reachability.
The internal contact transposition fixes $c$, and its sink-order property
preserves the size of the fibre of $c$ and the multiset of other fibre
sizes. These facts give the marked local identities for both values.

For a disconnected correction we put the selected weak block containing
$c$ last, and list the other weak blocks by their least vertices. Inside
each block we retain the vertex order. This relabeling fixes $c$.
It preserves the selected comparisons and the data in (3); the unused
natural edges between distinct selected blocks may then be discarded.

Thus the component collection gives a marked recurrence

\[
 V(P)[\beta]=\sum_i z_i V(P_i)[\beta],\qquad V=K,E,
 \tag{4}
\]

with the same integers $z_i$ for the two values. Every $P_i$ is a whole
component of a smaller diagram on the same vertex set as the prefix.

## Attaching an arbitrary component on the right

Let a second ordinary diagram occupy $[c,d]$. Assume that no natural
edge joins a vertex below $c$ to a vertex above $c$. The glued diagram
has exactly the natural and strict edges of its two factors. Fix a whole
component $T$ of this second diagram. We write $P*T$ for the selected
unions of one state of $P$ and one state of $T$.

![Right attachment and the merged fibre](figures/right-attachment.svg)

*Figure 4.* The upper dashed line indicates the vertex intervals, not a
natural edge. The diagrams share just $c$. Below, the canonical HRV chain
ending at $c$ and the chain beginning at $c$ concatenate. Their common
vertex, colored $\beta$, contributes one weight $x_\beta$.

**Attachment lemma.** The set $P*T$ is a whole flip component. Every
paired marked recurrence (4) gives

\[
 V(P*T)=\sum_i z_i V(P_i*T),\qquad V=K,E.
 \tag{5}
\]

*Proof.* Restrictions and unions are inverse bijections on selected
states. A triangle lies on one side of the cut, since its long edge
cannot cross the two interiors. Moreover, a forward path with endpoints
on one side cannot leave that side and return. Its cover tests are
therefore unchanged by restriction or union. A flip of the glued
diagram is exactly one factor flip, with the other factor fixed.
Every factor path lifts, and every glued path projects to factor paths.
This proves the assertion for whole components.

For a state $B$ on the attachment and a fixed color $\beta$ at $c$,
let $\widehat K(B)[\beta]$ be its coloring sum with the weight of $c$
omitted. Define $\widehat E(B)[\beta]$ in the same way on its canonical
HRV chains. These definitions use the product over vertices other than
$c$. Fixed-color restrictions and unions give

\[
 K(A*B)=\sum_\beta K(A)[\beta]\widehat K(B)[\beta].
 \tag{6}
\]

We next determine the HRV fibres of the union. For a left vertex $u$,
we have $H_{A*B}(u)=H_A(u)$ if $H_A(u)<c$, and
$H_{A*B}(u)=H_B(c)$ if $H_A(u)=c$. Every right vertex retains its HRV
from $B$. Indeed, a left vertex reaches the attachment precisely when
it reaches $c$. Thus the left fibre ending at $c$ merges with the
right fibre containing $c$, and all other fibres stay unchanged.
In their increasing chains, $c$ is the last left vertex and the first
right vertex. At color $\beta$, their merged factor is exactly
$x_\beta e_{p-1}(X_{<\beta})e_{q-1}(X_{>\beta})$. We obtain

\[
 E(A*B)=\sum_\beta E(A)[\beta]\widehat E(B)[\beta].
 \tag{7}
\]

For fibres of sizes $p$ and $q$, this merger is the familiar identity

\[
 \sum_\beta x_\beta e_{p-1}(X_{<\beta})e_{q-1}(X_{>\beta})
                       =e_{p+q-1}(X).
\]

We sum (6) and (7) over the product components, multiply the corresponding
identity (4) by $\widehat V(T)[\beta]$, and sum over $\beta$. This gives
(5) with exactly the coefficients $z_i$. The one-vertex attachment has
omitted weight $1$ for each allowed fixed color, so it is included.

## From the local relations to the component theorem

We apply induction on the lexicographic triple consisting of vertex
count, natural area, and area moment. Missing-corner deletion, alternating
corner deletion, and weak-block reordering give the smaller corrections.
We normalize to the selected-edge envelope; if it is proper, natural
area decreases. Disjoint natural components factor on fewer vertices.
The saturated connected path is an increasing chain, with value $e_n$.

For a connected common-cover component in a graph without articulation,
uniqueness permits the component collection: we add the other source
components to complete its total-edge layer, apply the local NN or DN
relation, then subtract their smaller corrections. NN yields target
layers $s$ and $s-1$; DN yields target layer $s$. DD and ND first unmark
the obstructing selected corner to use these same constructions. This
changes the representation of the component while preserving its states
and the two unweighted values.

For a graph with articulations, we take the initial path and the first
nontrivial block as the prefix. In area coordinates, an internal vertex
$v$ is an articulation exactly when $a_{v+1}=1$: an area of at least two
supplies the bypass edge $(v-1)(v+1)$. Thus we find the prefix by taking
the first run of area entries at least two, together with its initial
path. This prefix has the uniqueness just proved. The remaining graph
is a right attachment, and the attachment lemma applies to its marked
component recurrence.

At the cut $c$, the prefix has $a_c\geq2$. The next area in the source
is $1$, if present, whereas the appended prefix area is $0$. Both are
strict drops; every earlier comparison agrees. Hence the first-drop
contact used by the recurrence is the same in the prefix and source.
NN decreases natural area, and forward DN preserves area and decreases
area moment. Adding the same right attachment preserves these decreases.
Every resulting term is therefore a whole smaller component, with the
same integer coefficient for $K$ and $E$. Applying induction to these
terms gives the asserted equality.
