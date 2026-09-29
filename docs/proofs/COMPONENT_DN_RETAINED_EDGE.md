# Carrying a retained-edge DN flip back to the source

2026-09-28. We prove two arbitrary-exterior cases of the retained-edge
calculation in [joint DN repairs](COMPONENT_DN_JOINT_REPAIRS.md).
The unrestricted statement remains open. These are statements about actual
source components; they do not assume the component HRV formula.

## The configuration

Let w<x<s<t<z, with x=w+1, and write

    f=wz, r=xz, A=wt, p=xs, j=st, g=xt, q=wx.

All these edges lie inside the natural strict corner f. Let Q be a selected
source relation containing f,r,A, with p,j,g,q absent. Include all other
strict edges and the full exterior in Q. Suppose Q has no directed path

    x -> s,   s -> t,   x -> t.                       (1)

These are exactly the reachability conditions for the target flip retaining
g and exchanging p,j, after we replace the source corners e,f by the target
corners e',r. Here e=uw and e'=ux, with u<w, as in the DN step.
The corner change cannot affect a path between x,s,t.
In particular, p covers in Q+p and j covers in Q+j.

We seek a path of actual source flips from Q+p to Q+j, restoring every
other selected edge. Such a path proves equality of their source component
labels, as required to carry this target flip through the recurrence.

## When f covers

**Proposition.** If f is a cover in Q+p, then Q+p and Q+j belong to the
same complete source component. There is no further condition on the exterior.

We use the elementary cover test repeatedly: if a selected long edge ac and
a selected short ab both cover, and bc is absent, their exchange is actual
provided the new short has no bypass. The following sweeps verify every test.

**First make r a cover.** Consider all selected vz other than f,r for which
x reaches v in Q+p. Process them in decreasing order of v, replacing vz
by wv while retaining f. The processed vz covers: a bypass would end at
uz with u>v reachable from x, which was already removed. The cover of f
excludes a path from w to v, so wv is absent and the exchange is actual.
It leaves f a cover.

Throughout this sweep, reachability from x to vertices below z is unchanged:
new edges start at w<x, and deleted edges end at z. Thus the same decreasing
list remains valid, and the resulting r covers. Conditions (1) persist.
The edge A stays selected, since f covering and A selected exclude a path
from t to z, so tz was not on the list. The edge ws may have been added.

**Next make the short three-flip calculation available.** With f and r
covering, process in increasing order all selected wv, excluding ws,wt,
such that v reaches s or t. Replace wv by vz, retaining f. This is the
outgoing sweep proved in the joint DN note: the smallest remaining such v
makes wv a cover, and f remains a cover after the exchange.
It also leaves r a cover. Otherwise a new x-to-z bypass would use a new
vz, forcing x to reach s or t through v, contrary to (1). A path starting
with the selected xs would instead force s to reach t or itself.

Now A covers, and the only possible path from w to s is the edge ws itself.
Thus ws covers if selected. There is no path from s to z
because r covers with xs selected, and no path from t to z because f
covers with wt selected. If ws is absent, use

    xs -> sz [retain r],
    sz -> ws [retain f],
    ws -> st [retain A].

If ws is selected, use

    xs -> sz [retain r],
    ws -> st [retain A],
    sz -> ws [retain f].

The stated covers and absent paths make every flip actual. Both paths
replace p by j and preserve all other edges of the normalized relation.

**Restore the exterior.** First undo the outgoing sweep. Relative to each
forward state, p has been removed and j added. Deletion cannot spoil a
cover. The new st cannot bypass wv, since v<t, or bypass vz or f, since
there is no path from t to z.

Then undo the incoming sweep. Again st cannot bypass vz or f without a
t-to-z suffix. A bypass of wv using st would require a path from t to v.
But vz was selected in the original relation, which had no t-to-z path;
and none of our changes creates a path from t to a vertex below z.
Thus every reverse exchange remains actual. All exterior edges are
restored, proving the proposition.

## When r covers and t reaches z

**Proposition.** Suppose r covers in Q+p and Q has a selected path from
t to z. Then Q+p and Q+j belong to the same complete source component.
In this case f is redundant through A and that path.

Choose a saturated selected path

    t=v_0 < v_1 < ... < v_m=z.

Starting with the covering edge r=xv_m, for i=m-1,...,0 exchange
v_i v_{i+1} for xv_i, retaining xv_{i+1}. Each flip is actual: the
current long edge covers, the selected path edge covers, and an existing
path from x to v_i would contradict the cover of the current long.
The newly selected xv_i covers and supplies the retained edge for the
next step. Earlier changes cannot spoil a path-edge cover, since their
added edges start at x<t and their other changes are deletions.

We have now selected g=xt as a cover. The edge p still covers, since every
new edge xv_i ends at or after t>s. Conditions (1) also leave no s-to-t
path. We can therefore exchange p for j, retaining g.

Undo the path exchanges in reverse order. A new bypass of a tested long
xv_i using st would require an x-to-s path. There is no such path after
we delete p: it was absent in Q and the preparation only added edges from
x to vertices at or above t. A tested path edge starts at or above t, so
its cover cannot be affected by st. All reverse exchanges are actual,
and restore every path edge. This proves the proposition.

## Verification and scope

The existing independent Astra reviewer passed both propositions, including
the sweeps, path preparation, central flips and restoration with arbitrary
exterior. Every exchanged edge is normal inside the designated source corner.

Related Rust: `first_join_tree_lifts.rs --retained-exterior` reuses the
existing exact source component and cover-flip functions. It checks all
eligible target flips in source areas 011234 and 0112345: respectively
8 and 576 pairs, all with identical source component labels. The latter
fixture has 16,384 source orientations and 1,471 complete components.
This is finite evidence for the remaining cases, not their proof.

Receipts are under the external `dn-outer-sweep/` directory. No Lean source
or build is involved. Cases not covered by the two propositions, the
left-hand retained-e' case, and complete component reassembly remain open.
