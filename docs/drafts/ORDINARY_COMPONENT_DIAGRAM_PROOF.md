# Elementary expansions of ordinary flip components

We prove the component expansion by applying the local diagram relations to
whole components. The main step is to connect the states in which every
maximal corner is a cover. We then complete such a component to an entire
edge layer, apply the local relation, and remove the additional components by
induction. An endpoint attachment extends this construction to diagrams with
articulations.

## Selected diagrams and their two values

Let $G$ be an ordinary decorated natural diagram on $0,\ldots,n-1$.
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

For a whole flip component $C$, we sum either value over its states:
$K(C;X)=\sum_{A\in C}K(A;X)$ and
$E(C;X)=\sum_{A\in C}E(A;X)$.

**Theorem.** For every ordinary decorated natural diagram and every whole
flip component $C$, we have

\[
                     K(C;X)=E(C;X).
\]

The number $k(C)$ of selected normal edges is constant on a flip component.
Consequently its contribution to the LLT polynomial after the shift
$q\mapsto q+1$ is

\[
                q^{k(C)}\sum_{A\in C}e_{\lambda(A)}(X).
\]

## Connecting the states with corner covers

Let $M$ be the set of maximal natural corners. These corners form disjoint
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

*Figure 1.* The diagonal lists the ordered vertices $0<v<a<h=h_v$.
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
We apply the crossing slide in Figure 1. The core gains $ah_v$ and loses
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

*Figure 2.* The upper dashed line indicates the vertex intervals, not a
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
