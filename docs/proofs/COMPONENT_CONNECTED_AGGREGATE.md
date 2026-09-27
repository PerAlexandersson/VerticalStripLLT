# Connected aggregate extraction and the forest-component formula

Historical research note. The component theorem is now proved by the finite
route; see [the completion audit](../COMPONENT_COMPLETION.md). Open-status
sentences below record this earlier approach. Its additional auxiliary
claims are not automatically proved by the completed theorem.

Status: proved mathematically from the locally verified ordinary aggregate
theorem and the independently audited tree-connectivity theorem. Primary
found the partition-extraction argument; Astra checked the induced diagrams,
HRV factorization, coefficient isolation and forest extensions. These results
are not yet Lean declarations. The full component theorem beyond forests
remains open.

## Restricting to a vertex partition

Let D be an ordinary diagram on an ordered finite vertex set V, with natural
edges G and strict corners S. A selected orientation is S ⊆ A ⊆ G. Write
K_A(X) for its strict order enumerator, E_A(X) for the elementary monomial of
its actual HRV fiber sizes, and w(A) for its undirected connectivity partition.
We use t to count all selected edges. Multiplying the usual aggregate identity
by t^|S| gives

    Σ_A t^|A| K_A(X) = Σ_A t^|A| E_A(X).                 (AG)

This identity holds for every finite alphabet X, including the empty one.
No component formula is assumed.

Fix a set partition π of V. Order partitions by refinement, so w(A)≤π means
that every selected edge has both endpoints in one block of π. Define

    F_K(π) = Σ_(A : w(A)≤π) t^|A| K_A(X),
    F_E(π) = Σ_(A : w(A)≤π) t^|A| E_A(X).

If a strict edge crosses π, there is no such A and both sums are zero.
Otherwise, these orientations are exactly independent choices of selected
orientations on the induced diagrams D|B for B∈π, with every cross-block
normal edge unselected.

Each D|B, after increasing compression of its vertex labels, is a valid
ordinary diagram. Subinterval closure of G restricts to subinterval closure
in B. An original strict corner remains maximal: a containing natural edge
in the induced diagram would already contain it in D. Thus all restricted
strict decorations remain allowed. Blocks may interleave; contiguity is not
needed for this restriction.

For a selected state with no edges crossing π, every directed path stays in
one block. Its greatest reachable vertex, and hence its HRV fiber, is unchanged
by increasing compression of that block. The elementary monomial therefore
factors over blocks. Strict colorings and their vertex weights also factor,
and selected edge counts add. Consequently

    F_K(π) = ∏_(B∈π) Σ_(A_B in D|B) t^|A_B| K_(A_B)(X),
    F_E(π) = ∏_(B∈π) Σ_(A_B in D|B) t^|A_B| E_(A_B)(X).

Applying (AG) separately on each induced diagram proves F_K(π)=F_E(π).
This uses unrestricted orientation sums on those diagrams, not unknown
component identities.

## Equality at an exact weak partition

Let C_K(π) and C_E(π) denote the same sums restricted to w(A)=π. Then

    F_K(π) = Σ_(σ≤π) C_K(σ),
    F_E(π) = Σ_(σ≤π) C_E(σ).

Induction over the finite refinement order gives C_K(π)=C_E(π): subtract
the already equal terms for all strict refinements σ<π from the equality
F_K(π)=F_E(π). Equivalently, apply Möbius inversion on set partitions.
Only addition and subtraction in the integer polynomial ring are used.

In particular, taking π to have one block proves the connected aggregate
identity

    Σ_(A connected) t^|A| K_A(X)
      = Σ_(A connected) t^|A| E_A(X).                  (CA)

Every selected edge count can be extracted separately. This does not isolate
an arbitrary component: several complete components can occur in one such
coefficient. The next step identifies a coefficient where there is exactly one.

## Complete ordinary tree components

Let H be the interval envelope of an ordinary selected spanning tree. Make
every maximal edge of H strict, giving the saturated diagram on H. Its
selected orientations are precisely the sets with envelope H.

In (CA) for this diagram, the coefficient of t^(|V|−1) is precisely the sum
over spanning trees with envelope H: a connected simple graph on |V| vertices
with |V|−1 edges is a tree. By
[tree connectivity](COMPONENT_TREE_CONNECTIVITY.md), these trees form one
entire flip component. Therefore

    Σ_(A in that component) K_A(X)
      = Σ_(A in that component) E_A(X).                (Tree)

For the original normal-ascent variable, the same extraction is at exponent
|V|−1−|max H|, which is nonnegative because a tree containing max H exists.
The total-edge formulation avoids shifting exponents in the proof.

This proves (Tree) in any valid ordinary ambient diagram. A flip preserves
the selected envelope, so it stays within H. Its retained long edge forces
the exchanged short edges to lie in H. Conversely every flip in H is an
ambient flip. Every maximal edge of H occurs in every selected set having
that envelope and cannot be toggled. Original strict edges, being corners
of the ambient natural graph, are among these maximal edges whenever they
are selected. Saturating H therefore preserves the entire component and
both unweighted valuations.

The one-vertex case gives e₁, and the empty forest gives 1. When the alphabet
is empty and the vertex set is nonempty, both sides vanish. We do not divide
by a color variable or assume component symmetry.

## Complete ordinary and circular forest components

If a state is a forest, flips preserve its weak partition and selected edge
count within each weak block. Each block therefore stays a tree. Every flip
triangle is contained in one weak block. Covers between vertices of that
block are determined by its own selected relation, because directed paths
cannot leave the block. Thus the entire component is the Cartesian product
of its blockwise tree components.

We retain the selected envelope of **each** block before increasing
compression. The global envelope need not determine them when blocks
interleave. Apply (Tree) on every block and multiply; both K_A and E_A factor
over the same blocks. This proves the ordinary forest-component identity.

Every circular selected forest admits compatible integer vertex lifts.
The [compatible-lift theorem](COMPONENT_AMBIENT_REDUCTION.md) identifies its
entire actual circular component with an ordinary component after sorting
those lifts, preserving strict order enumerators and actual lifted HRV fibers.
It preserves the underlying undirected forest as well. Transporting the
ordinary result proves, for every circular forest component C and alphabet X,

    Σ_(A∈C) K_A(X) = Σ_(A∈C) E_A(X).                   (Forest)

All actual lifted-cover flips are included; no restricted local component or
projected-cover substitute is used. Since the component ascent is constant,
the common ascent weight may also be restored on both sides.

## Remaining obligation and formalization boundary

The proof covers forests of every size. Components containing undirected
cycles are still open, including balanced components. The structural proposal
AU_prime beyond trees and the unbalanced circular case remain separate
obligations in [the status map](../FLIP_COMPONENT_STATUS.md).

Related Lean: `VerticalStripLLT/Expansion.lean` supplies the unconditional
ordinary aggregate theorem; `Circular/ComponentSemantics.lean` supplies the
complete-component target. A future port needs induced-diagram compression,
factorization at a weak partition, finite partition inversion, tree
connectivity, and the compatible-lift transport. None is replaced by assuming
the component formula. No general symmetric-functions library is needed.
