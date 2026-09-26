# Direct ND through local NN, DN, and corner relations

This argument is locally formalized in `OneBounceNDGeometry`, `OneBounceND`,
and `OneBounceNDRecurrences`. It treats one bounce point only. Multi-bounce contact geometry is handled by elimination
and restart before applying these relations.

Let x=b(t), y=x+1, a=b(x)=b(y). The root strict edge is f:x→t, with length at
least two and a positive east gap at t. Row x is nonstrict and row y is strict;
write g:a→y and A=area(x). Then area(y)=A+1.

These hypotheses imply A≥1. Otherwise g has tail x, so strict-tail uniqueness
would identify g with f, forcing root length one. Likewise the residues of
y and t are distinct. Thus `LowerStrict.lowerStrict` moves the head of g from
y to x and shortens it by one. No global no-wrap or acyclicity assumption is
needed for the local polynomial identities.

Write F for either actual shifted model, namely shifted coloring or shifted
HRV expansion. Define:

- N: unstrict g in D, preserving its area;
- E: delete g's corner;
- S: lower g's head from y to x, namely `lowerStrict`;
- J: delete the newly strict corner at x from S;
- Q: shorten the root in D;
- N′, E′, J′, R: shorten the root in N, E, J, S respectively.

The four corner relations, two direct NN relations, and one direct DN relation
are

```
F(N)  = F(E)  + q F(D)       F(N′) = F(E′) + q F(Q)
F(E)  = F(J)  + q F(S)       F(E′) = F(J′) + q F(R)
F(N)  = (q+1) F(N′)         F(J)  = (q+1) F(J′)
F(S)  = F(Q).
```

Substitution and cancellation of q give

```
F(D) = q F(Q) + (q+1) F(R).
```

All root shortenings are valid. The modified row y cannot be the root or its
successor; the latter equality would identify the root with x. Lowering row x
can only improve the root gap when x is its successor. In J, both contact
areas equal A−1, so both boundaries equal a+1 and the NN hypotheses hold.
The root's boundary remains x. The DN successor of S restores g and shortens
f, giving exactly Q. Other residue coincidences are allowed: intermediate
strict graphs can be cyclic, and the local identities must retain that case.

The final targets have doubled half-square areas D−2 and D−4. The checked
`shortenStrict_doubledArea` supplies the first decrease. Head-left shifting
preserves strict cardinality and lowers the raw area sum by one, yielding the
second decrease after another root shortening.

The completed theorem `Diagram.exists_oneBounce_nd_reduction` exposes the
actual two-model identities and both area drops. `Diagram.expansion_of_oneBounce_nd`
is the semantic induction step. `StrictVals` supplies edge transport and full
diagram extensionality. The seven relations are proved independently for
coloring and HRV before cancellation; no recurrence defines either model.
Aristotle supplied the proof candidate, Luna ported the separate modules, and
primary checked the unchanged mathematical statements with the local toolchain.
