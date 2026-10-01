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
cover. Let $M$ be the set of these corners. Throughout the path arguments
we mark them all strict. They are selected in every state under consideration,
and a corner cannot be exchanged as a short edge, so this changes no permitted
flip along these paths. The corners form disjoint directed chains.
We write $r(u)$ for the last vertex in the chain containing
$u$. An anchor consists of all edges in $M$ and any additional natural
edges $uv$ satisfying $r(u)<r(v)$. Denote the union of all these allowed
edges by $A^*(G)$. A natural edge joining two vertices of the same corner
chain is itself a corner: any longer interval would contain the first
corner on that chain. Thus every normal edge has distinct terminal labels.
We call it good when these labels increase.

Every anchor is a common-cover state. Along a selected path the terminal
label increases at each normal edge and is unchanged at each corner.
A bypass of a corner would therefore use only corners, which cannot
bypass a single step of their chain.

**Preparation lemma.** Every common-cover state is joined by actual flips
to an anchor. We may retain every originally selected good edge throughout.
The path preserves the total selected size and the selected weak blocks.

*Proof.* We process the corner chains in decreasing order of their terminal
vertices. Let $U$ be the union of the chains already processed. We maintain
that no selected edge leaves $U$, and that all corners are covers at the
start of each chain. Initially $U$ is empty.

Let $B$ be the next chain, with terminal vertex $t$. We remove its selected
exits $vy$ with $r(y)<t$. Such an exit has $v<t$, since $v<y\leq r(y)<t$.
Let $h$ be the corner successor of $v$ in $B$. Maximality of the corner
$vh$ forces $v<y<h$: the edge $vy$ cannot properly contain $vh$.

Fix a vertex $v$ with an exit and choose its least exit head $y$.
Then $vy$ covers. Indeed, an alternate path from $v$ to $y$ cannot enter
$U$ and return. Its first edge cannot be the chain edge $vh$, since
$h>y$. Any other first edge staying outside $U$ would be an exit from
$v$ with a smaller head. Since $vh$ also covers, we can flip

\[
                       vy\longmapsto yh\qquad[vh].
                       \tag{P}
\]

Here and below, brackets give the retained edge. The new edge lies inside
$vh$, so it is natural and normal; its terminal labels increase.
The flip retains the cover of $vh$. Other corners of $B$ have intervals
with disjoint interiors, so their cover tests are unchanged. No selected
edge from $U$ changes. Each flip removes one exit and inserts none, so
the process terminates.

At the end no edge leaves $U\cup B$. Every inserted edge enters $B$.
An alternate path bypassing a corner outside $U\cup B$ therefore cannot
use an inserted edge: it would enter this union and never leave. Such
a bypass would already have existed before the chain was processed.
Corner covers inside $U$ are unchanged, and those in $B$ were retained
throughout. Thus all corner covers hold again, and we can continue with
the next chain.

When every chain has been processed, all selected normal edges are good.
Only edges with decreasing terminal labels were removed, so every original
good edge remains. Size and weak blocks are preserved by every actual flip.

## Crossing slides with the exterior restored

We next exchange selected edges across two crossing covers. This will allow
us to change the extra edges of an anchor while retaining all the others
at the endpoint of the path.

**Crossing-slide lemma.** Let $a<b<c<d$. Suppose $ac$ and $bd$ cover
in $A$, while $ab$ is selected and $cd$ is absent. Then actual flips join
$A$ to $A-ab+cd$, with every other selected edge restored. Both $ac$
and $bd$ cover at the endpoint.

*Proof.* Put

\[
 L=\{v:a<v<b,\ av\in A\},\qquad
 R=\{v:c<v<d,\ vd\in A\}.
\]

First sweep the edges $av$ for $v\in L$ in increasing order, replacing
$av$ by $vc$ across $ac$. At the time of its move, $av$ covers:
an alternate path would start with an edge from $a$ to a smaller vertex,
and these edges have already been removed. The retained $ac$ remains
a cover after each flip. Every changed edge has its smaller endpoint below
$b$, so the changes
do not affect any path inside $[b,d]$; hence $bd$ continues to cover.

Next sweep $vd$ for $v\in R$ in decreasing order, replacing $vd$ by
$bv$ across $bd$. An alternate path from $v$ to $d$ would end with
an edge from a larger vertex, already removed. These are actual flips
retaining $bd$. Every changed edge has its larger endpoint above $c$, leaving all
paths in $[a,c]$ unchanged, so $ac$ continues to cover as well.

Now $ab$ covers, since there is no selected edge from $a$ into $(a,b)$.
The edge $bc$ is absent: if it had been selected originally, $ab,bc$
would bypass $ac$, and neither sweep inserts it. We perform the two flips

\[
              ab\longmapsto bc\quad[ac],\qquad
              bc\longmapsto cd\quad[bd].                       \tag{S}
\]

After the first, $bd$ still covers. A newly created bypass would have
to start with $bc$, but there is no path from $c$ to $d$: the edge
$cd$ is absent, and the right sweep has removed all incoming edges
to $d$ from $(c,d)$. Thus the second flip is actual. It leaves $bd$
covering and preserves the cover of $ac$, since it removes $bc$ and
inserts an edge leaving $c$.

We restore the right sweep first, in reverse order. For $v\in R$, the
net change $ab\mapsto cd$ affects no edge wholly inside $[b,v]$:
$ab$ starts below $b$, and $cd$ ends above $v$. Hence the cover test
for each $bv$ agrees with its cover test when we reverse the original
right sweep. Starting with the cover $bd$, each reverse flip is actual
and keeps $bd$ covering. These changes affect no path in $[a,c]$.

Finally restore the left sweep in reverse order. For $v\in L$, the net
change affects no edge wholly inside $[v,c]$, so the cover test for $vc$
agrees with its test in the reversed left sweep. Starting with the cover
$ac$, these reverse flips are actual. They do not change paths in $[b,d]$.
Every exchanged edge lies properly inside $ac$ or $bd$, so it is normal
throughout. We obtain exactly $A-ab+cd$ in $2+2|L|+2|R|$ flips.

![Sweeping and restoring the exterior of a crossing slide](figures/crossing-sweeps.svg)

*Figure 2.* We take $a=0,b=2,c=3,d=5$ and retain the strict corners
$03,14,25$. The two sweeps exchange $01\mapsto13$ and $45\mapsto24$.
The central flips give $02\mapsto23\mapsto35$, after which we restore
$24\mapsto45$ and $13\mapsto01$. Underlines mark the retained covers
$03$ and $25$. The corner $14$ may be redundant between the two endpoint
states. Each picture specifies one selected state; the arrows denote paths
of flips, and do not assert equality of individual state values.

## Rearranging edges between two corner chains

For a natural normal edge $uv$, a corner $uh$ gives the short-edge link
$uv\longrightarrow vh$. Maximality of $uh$ implies $v<h$, and $vh$
is natural because it lies inside $uh$. This link exchanges the terminal
labels of the two endpoints. Each normal edge has at most one successor
and at most one predecessor under these links. Both endpoints strictly
increase along a link, so the links form disjoint finite paths.

For any two corner chains there is at most one such path. To see this,
let $uv$ be its first edge. If $v$ had a corner predecessor $p$, then
$p<u$: otherwise $uv$ would equal or properly contain the corner $pv$.
The edge $pu$ would be a predecessor, a contradiction. Thus $v$ is the
first vertex of its chain, and $u$ belongs to the chain starting earlier.
There is at most one possible $u$ in that chain below $v$. Indeed, if
$u<u'<v$ were two choices, the natural interval $uv$ would properly
contain the corner from $u$ to its successor, which is at most $u'$.

Good and non-good edges alternate on each short-edge path, since a link
exchanges its two distinct terminal labels. Consecutive good positions
therefore have the form $ab,cd$ with $a<b<c<d$ and corners $ac,bd$.
In an anchor, both corners cover. Whenever exactly one of $ab,cd$ is
selected, the crossing-slide lemma exchanges it for the other, restoring
every exterior edge. The endpoint is another anchor.

**Parallel-edge lemma.** Suppose two anchors select the same number of
good normal edges between each pair of corner chains. Then actual flips
join them.

*Proof.* List the good positions for one pair in their short-edge order.
We repeatedly exchange an occupied position followed by a vacant one.
The sum of the occupied position indices strictly increases and is bounded,
so we reach the configuration occupying the last positions of that list.
It depends only on the number selected. Each exchange restores every other
edge, so we can do this separately for every pair of chains. Both anchors
reach the same selected diagram. We reverse the path from the second.

**Two-chain lemma.** If there are at most two corner chains, all
common-cover states of a fixed total selected size lie in one flip component.

*Proof.* Prepare both states to anchors. If there is at most one chain,
the only anchor is $M$. With two chains, every selected normal edge joins
that one pair. Equal total size gives equal numbers of normal edges,
so the parallel-edge lemma connects the anchors. Reverse the second
preparation path.

![Rearranging selected edges between two corner chains](figures/two-chain-packing.svg)

*Figure 3.* The corner chains are $0,2,4,6$ and $1,3,5$. The good
normal positions are $12,34,56$. Each arrow is the crossing-slide path
between the two indicated anchors, with every other selected edge restored.
Both states on the left reach the anchor whose two selected good edges
occupy the last two positions. Each cell picture fixes a selected state;
these path arrows are not identities of individual state values.

## The complete-diagram base

We now work in the complete natural diagram on $0,\ldots,N$, with
$N\geq1$. Its only maximal corner is $0N$.

**Complete-diagram lemma.** Connected states in which $0N$ covers belong
to one flip component at each fixed total selected size.

We first introduce the selected chain

\[
                    P_N=\{0N,12,23,\ldots,(N-1)N\},
\]

then rearrange its extra edges. We call these extra edges chords; their
positions are $ij$ with $1\leq i<i+1<j\leq N$.

**Introducing the chain.** Preparation gives an anchor consisting of
$0N$ and a connected selected graph $H$ on $1,\ldots,N$. Whenever
$ab,ac$ are two outgoing covers of $H$, with $a<b<c$, flip
$ab\mapsto bc$ retaining $ac$. This is an actual flip: $bc$ is
absent since otherwise $ac$ would not cover. The sum of the tails of
the selected edges strictly increases, so these moves terminate.

The final cover graph has at most one outgoing edge at each vertex.
It is connected, since removing redundant edges preserves weak connectivity.
An undirected cycle would have a least vertex with two outgoing covers,
so the graph is a tree. It has unique sink $N$. Replacing a selected
edge repeatedly by shorter paths until every edge covers shows that its
endpoints are a vertex and an ancestor in this tree.

Suppose $i<j$ are children of $N$. Each has exactly one outgoing
selected edge, to $N$. The following four flips replace $iN$ by $ij$:

\[
 iN\mapsto0i\ [0N],\quad jN\mapsto0j\ [0N],\quad
 0i\mapsto ij\ [0j],\quad 0j\mapsto jN\ [0N].       \tag{T}
\]

For the first two flips, removing a child's sole outgoing edge makes it
a sink. Thus the new edge from zero cannot bypass $0N$. At the third
flip both $i$ and $j$ are sinks, so $0i,0j$ cover. After that flip
zero is adjacent only to the sinks $j,N$, so $0j,0N$ cover and the
final flip is actual. Incoming selected edges
cannot change these cover tests. The new tree replaces the branch
$i\to N$ by $i\to j\to N$, and all old shortcut edges still join
ancestors.

The greatest child of $N$ is $N-1$. Repeatedly apply (T) with $j=N-1$
until it is the only child. The restriction of $H$ to $1,\ldots,N-1$
is then connected. Flip $(N-1)N\mapsto0(N-1)$ across $0N$ and apply
the chain construction inductively inside $0,\ldots,N-1$. Every local
flip remains actual: a forward path between two vertices in this interval
cannot leave through $N$ and return. At the local endpoint, zero has
only the edges $0(N-1),0N$, and $N-1$ has no outgoing edge. Hence
both zero-edges cover, and we flip $0(N-1)$ back to $(N-1)N$.
Starting with $N=1$, this constructs $P_N$ with no other edge at zero.

![Four flips merging two children](figures/complete-child-merge.svg)

*Figure 4.* The four flips in (T) replace $iN$ by $ij$. The pictures
fix all selected edges on $0,i,j,N$; the remaining selected edges are
the same at both endpoints. At the source, zero is incident only to
$0N$, and the only outgoing selected edge of either child is its edge
to $N$. Arbitrary incoming edges at the children are allowed.

**Using a smaller interval.** Consider two chain states which agree
outside the ordered vertex set $\{0,a,a+1,\ldots,b\}$, where
$0<a\leq b\leq N$. We can lift a path between their restrictions
while restoring the entire exterior.

To do so, open the chain in decreasing order $j=N-1,\ldots,b$:

\[
                j(j+1)\mapsto0j\quad[0(j+1)].                 \tag{O}
\]

The adjacent short edge covers. Before its move, every selected edge
from zero ends at or above $j+1$. After the move the newly reached
vertex $j$ cannot reach $j+1$, since their adjacent edge was removed.
Thus each flip is actual, regardless of the chords.

The opened zero-row has precisely the heads $b,b+1,\ldots,N$.
The restriction to $\{0,a,\ldots,b\}$ is a smaller chain state with
corner $0b$. A forward path testing an edge with both endpoints in
$[a,b]$ stays inside this interval. For an edge from zero, a path cannot
enter a vertex below $a$, since no zero-edge goes there; it cannot return
from a zero-edge ending above $b$. These facts remain true during any
path in the smaller diagram, so all its flips lift. Open the target ambient
chain state by the same procedure. Its restriction is the target of the
local path, and its exterior agrees with the source opening. We can therefore
finish by reversing that target opening in increasing order. This restores
the exterior exactly.

**Rearranging the chords.** We prove the lemma by strong induction on $N$,
using the chain construction above for both endpoints. For $N\geq5$,
apply the smaller-interval construction to $[1,N-1]$ and $[2,N]$.
By induction, within either interval we may rearrange the selected chords
at fixed count, leaving every other edge fixed at the endpoint.

The two sets of chord positions cover all positions except $1N$, and
their intersection contains $24$. Thus exchanges within these sets connect
all equal-size chord subsets with the same selected status of $1N$.
If no one interval contains both positions of an exchange, we route
through $24$, which is distinct from both. If $24$ is vacant, move the selected edge there first;
if occupied, move it to the vacant destination first. In either case
the second exchange restores the original status of $24$.

It remains to change the $1N$ status. Suppose that $1N$ is absent and
both $13$ and $2N$ are selected. Sweep every selected incoming edge
$iN$, $0<i<N$, in decreasing $i$, replacing it by $0i$ across $0N$.
When $iN$ moves, all incoming edges with larger tails have been removed,
so $iN$ covers. The zero-neighbors created earlier are larger than $i$
and cannot reach an unswept incoming tail; therefore $0N$ covers too.

Now $01$ is absent and $02$ is selected. Flip $12\mapsto01$ across
$02$. The retained $02$ covers because no selected zero-edge has a
smaller head. Reverse the incoming sweep in increasing order, including
the new edge $01$. Each zero-edge being moved has the smallest remaining
head, and all restored incoming tails are smaller than that head. This
gives actual reverse flips and the exact state

\[
                            A-12+1N.                          \tag{U}
\]

We repair the missing chain edge using $13$. Open the chain down to $3$
by (O). On $0,1,2,3$ the selected edges are $03,13,23$, with $12$
absent. Apply the four flips (T) with $i=1,j=2,N=3$, then close the
chain. The smaller-interval cover argument permits all the fixed exterior
chords. We have restored $12$ and removed $13$, obtaining

\[
               A\longmapsto A-13+1N
               \qquad(13,2N\in A,\ 1N\notin A).              \tag{U'}
\]

Let $Q=\binom{N-1}{2}$ be the number of chord positions. If the chord
count $c$ satisfies $2\leq c\leq Q-1$, the fixed-$1N$ rearrangements
let us select $13$ and $2N$ in an outer-absent state. Move (U') then
joins the two possible $1N$ statuses. At counts $0$ and $Q$ there is
only one chord set.

For $c=1$, start from $P_N+13$ and open the chain down to $2$.
Perform

\[
                    13\mapsto01\ [03],\qquad
                    01\mapsto1N\ [0N],
\]

then close the chain. All vertices $2,\ldots,N$ are sinks while the
chain is open, and there are no other chords, so both retained longs
and exchanged shorts cover. The endpoint is $P_N+1N$. Together with
the fixed-status rearrangements, this connects every single-chord state.

For completeness, the induction has the following explicit bases. If
$N\leq3$, there is at most one chord position. For $N=4$, the positions
are $13,14,24$. In the table, a triple $abc$ means the flip exchanging
$ab$ and $bc$ while retaining $ac$; its direction is determined by the
current selected state. Each row starts with $P_4$ plus the indicated
left chord set and ends with $P_4$ plus the right chord set.

| Chord sets | Successive flip triples |
| --- | --- |
| $\{13\}\longrightarrow\{14\}$ | $034,023,013,014,023,034$ |
| $\{14\}\longrightarrow\{24\}$ | $034,124,014,023,012,023,034$ |
| $\{13,24\}\longrightarrow\{14,24\}$ | $034,024,012,014,024,013,023,012,023,034$ |
| $\{14,24\}\longrightarrow\{13,14\}$ | $034,023,012,013,023,124,034$ |

Inspection of these selected diagrams verifies the short and long covers
at each step. The rows connect every one- and two-chord subset; the zero-
and three-chord subsets are unique. This starts the induction. Finally,
we reverse the chain construction for the second original state.

## Removing one good edge

We justify the removable-edge hypothesis needed below directly in the
good-edge graph $A^*(G)$. Connectivity in this paragraph is undirected.

First, replacing the natural graph by $A^*(G)$ preserves connectivity
within any specified union of corner chains. For a natural normal edge
$uv$ with $r(u)>r(v)$, let $uh$ be the corner successor of $u$.
As in preparation, $u<v<h$. We replace the edge $uv$ in a walk by
the two edges $uh,hv$, traversing the latter backwards. The corner $uh$
and good edge $vh$ belong to $A^*(G)$, and the replacement visits only
the two original corner chains. All other natural edges already belong
to $A^*(G)$.

**Chain-deletion lemma.** If a connected ordinary natural graph has at
least three vertices and remains connected after deleting any single vertex,
then deleting all vertices of one
corner chain leaves the other vertices connected in $A^*(G)$.

*Proof.* Every pair of vertices at distance one or two is a natural edge.
An absent adjacent edge would, by closure under subintervals, exclude every
edge across its cut and disconnect the graph. If $(i-1)(i+1)$ were absent, closure
under subintervals would exclude every natural edge from below $i$ to
above $i$. The vertex $i$ would be an articulation.

Consecutive vertices cannot belong to the same corner chain. Their edge
would be a corner, but it lies properly in a natural edge of length two:
extend it to the left unless its first vertex is zero, and to the right
in that case. Thus removing a corner chain never removes two consecutive
vertices, and at least one vertex survives. Consecutive surviving vertices
differ by at most two and hence
are joined by a natural edge. They form a path through all remaining
vertices. Replace its non-good edges by the two-edge walks above; these
walks avoid the removed chain.

**Removable-edge lemma.** Under the same hypotheses, suppose there are
at least three corner chains. Deleting any good normal edge from
$A^*(G)$ leaves it connected.

*Proof.* Let the edge be $uv$, and choose a vertex $w$ in a third chain.
By the chain-deletion lemma, a path joins $u$ to $w$ while avoiding the
chain of $v$, and a path joins $w$ to $v$ while avoiding the chain of $u$.
Neither path uses $uv$, so their concatenation goes around that edge.
The full graph $A^*(G)$ is connected by the natural-edge replacement
argument. Replacing every use of $uv$ by this walk proves the result.

Equivalently, contraction of the corner chains gives a graph which remains
connected after deleting any one of its vertices. The explicit avoiding
paths above also lift directly to the good-edge graph, as needed for the
initial-vertex construction.

## Initial-vertex inheritance

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

*Figure 5.* The diagonal lists the ordered vertices $0<v<a<h=h_v$.
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
We apply the crossing slide in Figure 5. The core gains $ah_v$ and loses
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
It has at least three chains outside the base cases. The removable-edge
lemma therefore applies to every matching edge $d_v$, verifying the
remaining hypothesis of the initial-vertex lemma.

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

*Figure 6.* The blank cells and permitted exterior edges are summed over.
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

*Figure 7.* The upper dashed line indicates the vertex intervals, not a
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

## Choosing the prefix and the first contact

Write $b_i=i-a_i$ and append $a_n=0$ for the terminal comparison.
The boundaries $b_i$ are nondecreasing. A corner ending at $i$ is
$b_i i$, and it exists exactly when $a_i>0$ and $a_{i+1}\leq a_i$.
We call a diagram saturated when every natural corner is marked strict.

The natural graph is connected precisely when $a_i>0$ for every $i>0$.
These inequalities supply the adjacent-edge spanning path. Conversely,
if $a_i=0$, every later boundary is at least $i$, so no natural edge
crosses the cut between $i-1$ and $i$.

**Prefix lemma.** In a connected ordinary diagram, suppose some $a_j\geq2$.
Choose the least such $j$, put $b=j-2$, and choose the least $c\geq j$
such that $c=n-1$ or $a_{c+1}=1$. The induced prefix on $[0,c]$
consists of the path $[0,b]$ followed by a graph on $[b,c]$ without
articulation. The rest of the diagram is a right attachment at $c$.
The prefix and original diagram have the same first strict decrease in
area, with terminal area zero appended to each.

*Proof.* For an internal vertex $v$, the equality $a_{v+1}=1$ makes
$b_{v+1}=v$. Every later boundary is at least $v$, so no natural edge
joins a vertex below $v$ to a vertex above $v$. Thus $v$ is an articulation.
If $a_{v+1}\geq2$, the edge $(v-1)(v+1)$ bypasses $v$ in the
adjacent-edge spanning path. Removing $v$ leaves all other vertices
connected. Removing either endpoint also leaves an adjacent-edge path.
This proves the articulation test.

By minimality of $j$ and the area growth bound, $j\geq2$,
$a_{j-1}=1$ and $a_j=2$. Every earlier positive area is one.
Starting at $a_{b+1}=1$, the growth bound gives $a_i\leq i-b$ for
all $i>b$. Hence every natural edge ending above $b$ starts at least
at $b$. The initial path meets the remaining graph only at $b$.
After reindexing $[b,c]$ from zero, its local areas begin $0,1,2$;
all subsequent areas through $c$ are at least two. The articulation
test applies.

If $c<n-1$, the boundary at $c+1$ is $c$, and monotonicity excludes
all natural edges between the interiors of $[0,c]$ and $[c,n-1]$.
If $c=n-1$, the attachment is the single vertex $c$. The inherited
strict edges stay corners in their respective factors: a larger
containing natural interval there would already contradict their
maximality in the source.

Finally, $a_c\geq2$. At $c$, the original diagram compares $a_c$
with $1$ when the attachment is proper, whereas the prefix compares
it with its appended $0$. Both comparisons are strict decreases.
All earlier comparisons agree, so their first strict decreases agree.

![A prefix and its right attachment as restricted sums](figures/prefix-attachment.svg)

*Figure 8.* The source areas are $(0,1,1,2,3,2,1,2,1)$.
The first area at least two occurs at $j=3$, so $b=1$ and $c=5$.
The prefix has the initial edge $01$ followed by the block $[1,5]$;
the attachment is $[5,8]$. The first strict area decrease is at $t=4$
in both prefix and source. For a whole component $C=P*T$, each picture
denotes the indicated restricted sum. The attachment value $\widehat V$
omits the weight of the shared vertex $5$. The displayed identity holds
for $V=K$ and $V=E$ separately.

We now choose the local relation in the prefix. Rows are called N or D
according as their incoming corner is not strict or is strict. In
particular, row zero is N.

**First-contact lemma.** Let a connected saturated ordinary diagram have
at least one non-adjacent natural edge. Let $t$ be the first index with
$a_{t+1}<a_t$, and set $x=b_t$, $y=x+1$. Then $xt$ is a strict
corner of length at least two, and $x,y$ form an eligible NN, ND, DN
or DD contact at that corner.

*Proof.* The appended zero guarantees a strict decrease. Before $t$ the
areas are nondecreasing. If $a_t=1$, connectedness would force $t=n-1$
and all positive areas would be one, contrary to the non-adjacent edge.
Thus $a_t\geq2$ and $0\leq x<y<t<n$. The strict decrease makes
$xt$ a corner and gives its terminal gap.

Since $y<t$ precedes the first decrease, we have
$a_x\leq a_y\leq a_x+1$. If $a_y=a_x+1$, then $b_y=b_x$ and
row $x$ has no corner. We have NN or ND according to the flag at $y$.
In the ND case $a_x>0$: otherwise its strict corner would be $xy$,
properly contained in the natural corner $xt$.

If $a_y=a_x$, then $a_x>0$, since the subedge $xy$ of $xt$ is natural.
Put $u=b_x$. The corner $ux$ is strict, and

\[
                  u<x<y<t,\qquad b_y=u+1.
\]

This gives DN or DD according to the flag at $y$. In DD its incoming
strict corner is $(u+1)y$. The required heads are distinct and the
local area bound follows from $a_x+1\leq x+1=y<t$.
These two cases give the contact geometries used in (LNN) and (LDN).

There is no strict edge leaving $y$. Before $t$, boundary increments
are zero or one, so the corner tails encountered there are exactly
$0,\ldots,x-1$. The corner at $t$ has tail $x$, and the strict area
decrease gives $b_{t+1}\geq x+2$. All later tails are at least $x+2$.
Thus, after unmarking its incoming corner when necessary, $y$ has no
incident strict edge. The adjacent contact exchange has the required
exterior strict-edge correspondence.

The four cases reduce as follows:

| Contact | Change of marking | Relation |
| --- | --- | --- |
| NN | None | NN |
| ND | Unmark the incoming corner at $y$ | NN |
| DN | None | Forward DN |
| DD | Unmark the incoming corner at $y$ | Forward DN |

In the ND and DD cases, the original component still selects the
unmarked corner throughout. Its selected status is invariant under flips,
so the component is one whole component of the newly marked diagram.
The change of marking preserves its full selected relations and its
unweighted values; it invokes no induction hypothesis.
We retain this unmarked decoration in the prefix and its recurrence;
we do not mark it strict again before applying NN or DN.

For the induction measure, put

\[
          A(D)\coloneqq\sum_i a_i,\qquad
          M(D)\coloneqq\sum_i i a_i.
\]

NN decreases $A$ by one. In forward DN, the natural edge $xt$ is
replaced by $uy$. Since $b_y=u+1$, the pair $uy$ is not natural
in the source; increasing $a_y$ by one makes it natural in the target.
Thus

\[
 a_y\longmapsto a_y+1,\qquad a_t\longmapsto a_t-1,
 \qquad A(R)=A(D),\qquad M(R)=M(D)-(t-y)<M(D).       \tag{8}
\]

The source corrections in (L) decrease natural area. If the prefix on
$[0,c]$ is glued to a fixed attachment $T$, indexed locally from zero,
write $A(P),M(P)$ and $A(T),M(T)$ for their ambient diagram measures. Then

\[
 A(P*T)=A(P)+A(T),\qquad
 M(P*T)=M(P)+M(T)+cA(T).                             \tag{9}
\]

There are no natural edges between the two interiors, and the attachment's
local area at the shared vertex is zero. Every other
attachment column shifts its index by $c$, proving (9). Thus every
strict decrease in the prefix pair $(A,M)$ remains a strict decrease
after the same attachment is glued on.

## Proof of the ordinary component expansion

We induct on $(n,A(D),M(D))$ in lexicographic order. The empty selected
diagram has value $1$, and the single vertex has value $e_1(X)$.
All equalities below are unweighted and hold for every finite alphabet.

Normalize the component to its selected-interval envelope. If any natural
edge is removed, natural area decreases, and induction applies to the
whole component in the smaller diagram. Otherwise mark the selected
maximal corners strict, preserving the component and both its values.
We may therefore assume the diagram is saturated.

If the natural graph is disconnected, its connected components occupy
disjoint consecutive intervals. Every flip stays in one interval, so a
whole flip component is the product of its restrictions to these diagrams.
Colorings on disjoint vertex sets factor, and the highest reachable fibres
stay in their own intervals. Thus both $K$ and $E$ are products of the
corresponding component values. Each factor has fewer vertices, and
induction proves the result.

Suppose the natural graph is connected. If it is a path, saturation
requires every adjacent edge. There is one selected state, the increasing
chain; its strict colorings and its single HRV fibre both give $e_n(X)$.
Otherwise the prefix lemma supplies an initial path followed by the first
block without articulation, and a right attachment $T$.

If the selected graph is disconnected, use weak-block reordering. If the
component has no simultaneous-cover witness, use the alternating deletion
formula (C). Every term is a whole component of smaller natural area,
with the same coefficient for $K$ and $E$, so induction proves its equality.
It remains to treat a connected component with a simultaneous-cover witness.

Write it as $P*T$ using whole-component factorization at the cut. Both
selected factors are connected. Restricting the simultaneous-cover witness
gives such a witness in the prefix: all its maximal corners are the source
corners ending in the prefix, and their cover tests are internal. The
initial-path extension of common-cover uniqueness therefore applies to $P$.

Choose the prefix's first strict area decrease. It is the same contact as
in the source. Apply the marking change in the table and then the marked
NN or DN component recurrence. Completion of the prefix layer and the
three smaller corrections give a finite list of integers $z_i$ and whole
prefix components $P_i$ such that, for every endpoint color $\beta$,

\[
                    V(P)[\beta]=\sum_i z_i V(P_i)[\beta],
                    \qquad V=K,E.
\]

All prefixes have the same vertex set. Each target is smaller in $(A,M)$
by (8) or a source correction. Attach the same $T$ to each term. The
attachment lemma gives whole components $P_i*T$ and the two identities
with these same integers $z_i$. Equation (9) preserves every strict
decrease, so induction gives $K(P_i*T)=E(P_i*T)$ for every term. Their
signed sums give $K(P*T)=E(P*T)$.

We finally restore the original normal-edge weight $q^{k(C)}$, which is
constant on the component before any change of marking. The elementary
coefficient of its unweighted value counts states having the corresponding
HRV fibre partition, as asserted.
