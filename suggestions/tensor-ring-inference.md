# Tensor ring instance inference

In the pinned Lean 4.34 / Mathlib build, synthesizing `Ring (K ⊗[ℤ] WordAlgebra V)`
succeeds, but inferring its distributivity classes inside rewrites can fail.
This cost repeated checks during scalar-extension integration.

`Components/WordProof/WordScalars.lean` supplies a local instance equal to
`Algebra.TensorProduct.instRing`. This makes superclass inference reliable,
without changing the mathematical structure or any global instance priorities.
Explicit `(V := Fin n)` arguments also avoid expensive unfolding of the word
quotient when applying its polymorphic lemmas.

Give each local instance an explicit distinct name: Lean still exports its
declaration even though its instance attribute is local. Two modules with the
same anonymous instance name failed when imported together; distinct names
fixed the combined build.

Before extending this pattern elsewhere, reduce it to a small upstream example
and check whether the pinned Mathlib tensor instance hierarchy already has a fix.
Do not change shared dependencies merely to work around this local issue.
