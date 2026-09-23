# Native exponential and logarithm on the original observation group — F61

Historical checkpoint. F62 supplies a common fixed-presentation bound
for the native weak-basis data and both arrays, together with finite
bounded rational kernel families. See ORIGINAL_BOUNDED_WEAK_BASIS_INTERFACE.md.

F61 adds 11 theorem declarations to F60's 1620. Full project verification
is recorded in verification/result.json, build.log and axioms.log.
P0 and WeightedCapture remain unproved.

## Exact obstruction and tangent specification

An equality of totalized derivative values does not assert an actual
derivative. The exact absolute-value example proves that its totalized
derivative at zero is zero although it has no zero derivative there.
This is a derivative-interface obstruction, not a counterexample to P0.

OriginalNativeSubgroup retains the actual identity at time zero, the
original multiplication law at all real times, MDifferentiableAt at zero,
and the native manifold differential applied to scalar tangent one.
The coordinate HasDerivAt condition is proved equivalent to that pair of
native differential conditions. The final theorem quantifies over the
actual Mathlib GroupLieAlgebra of the original observation group.

## One selection of original witnesses

F58 already constructed the subgroup family internally, but its exported
time-one equivalence omitted the subgroup uniqueness facts. The stronger
original_integral_basis_time_one_equiv_with_subgroups retains these facts
with that very same integer basis, real basis, operator tensor, nilpotency
exponent and rational fiber polynomials. Its old interface is now a proved
projection, preserving existing consumers.

The analogous F59 strengthening carries the same subgroup family through
both rational coordinate arrays and the actual full logarithm. Again the
old interface is a projection. No independent existential selections are
identified, and no subgroup existence or uniqueness premise is added to
the original structural assumptions.

## Native universal property and all real times

Every full tangent is decomposed into its original base coordinates and
its unrestricted original observation component using the same real
basis. The constructed path is the unique actual original-group subgroup
with that native tangent, and its time-one value is logCoord.symm.

Real rescaling is proved for all scalars, including zero and negative
scalars. Uniqueness then identifies every value of the original path:

```
gamma(t) = logCoord.symm(t * v).
```

Thus the curve t ↦ logCoord.symm(t * v) itself has the actual original
subgroup law and native initial tangent v, and every other subgroup with
that native tangent is equal to it on the entire real line. This is the
subgroup universal-property identification of the exponential; no external
exponential theorem or separately chosen exponential map is assumed.

## Same-basis complete qualitative assembly

original_full_native_exponential_and_lattice constructs, from the original
rational joint law, strict triangular law, integer coordinate lattice and
rational original observation basis:

- One compatible full integer/real basis and original differential tensor.
- The actual time-one formula for every unrestricted base tangent and
  original observation.
- A global equivalence logCoord, with both directions given by literal
  rational arrays in the original coordinates and with logCoord(1)=0.
- The actual smooth Lie group and rational structure coefficients of its
  native tangent basis.
- The native exponential subgroup universal property for every full
  tangent and every real time.
- Smoothness of logCoord and its inverse on the original manifold.
- Both denominator inclusions for the entire original H lattice, with
  one positive denominator preceding all integer vectors and lattice elements.

The smoothness proof applies directly to the actual global chart and the
proved rational arrays. The original group, its topology, original
observations and entire original integer lattice are retained. This is an
exponential/logarithm on H, not on H/Gamma_H or the circle frequency space.

## Remaining core obligations

The qualitative native exponential/logarithm identification left open at
F60 is now assembled. The constructed rational basis is not thereby an
adapted Malcev basis with uniform quantitative control over all later
descent states. Uniform heights, adapted bases, external metric/test/
filtration/interval matching, general structural descents and quantitative
termination remain open. These are internal proof obligations even where
external deep theorems are allowed as explicit inputs.

The original-frequency realization must still retain all original labels,
circle root branches, vertical quadratic freedom, weights and full
responses. Neither the original P0 lower-bound quantifiers nor the Phase12
finite-list-before-data quantifiers are weakened. Final WeightedCapture/P0,
P2-CSE and U0 remain open; the historical twelve invalid three-dimensional
composite applications remain deferred and unused.

The new modules are OriginalSubgroupTangent, OriginalRationalSmoothEquiv,
OriginalNativeExponential and NativeTangentObstruction. Two existing
time-one/logarithm modules have stronger same-witness interfaces.
