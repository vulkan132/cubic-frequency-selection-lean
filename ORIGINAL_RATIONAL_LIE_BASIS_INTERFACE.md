# Original tangent space, rational Lie basis and full H lattice — F60

Checkpoint date: 2026-09-23. F60 adds 19 theorem declarations to F59's
1601. P0 and WeightedCapture remain unproved. The complete audit is
recorded in verification/result.json, build.log and axioms.log.

## Convention check

The existing originalCoordinateVelocity differentiates the first input
of multiplication and gives a right-invariant field. Mathlib's
GroupLieAlgebra uses mulInvariantVectorField and left multiplication.
The exact polynomial x3+y3+x1*y2 records why they cannot be identified:
the first-input e1 partial at the identity is the other point's y2,
whereas the second-input e1 partial is zero. The new obstruction theorem
proves both identities and nonvanishing of y2. It is not a P0 refutation.

## Actual differential and bracket

The original singleton chart and its inverse are identified with the
original coordinate homeomorphism and its inverse. The derivative of a
self-map's coordinate conjugate equals its actual manifold differential
in this chart. The chart and inverse-chart differentials are identity
maps on the corresponding tangent coefficients. These identities prove
that the actual manifold Lie bracket is the analytic bracket of the
coordinate vector fields.

For a curve gamma, HasMFDerivAt is equivalent to HasFDerivAt of
coord composed with gamma, with the same continuous linear map.
A coordinate derivative v therefore gives native manifold differential
applied to the scalar tangent 1 equal to v. All of these statements use
Mathlib's actual manifold definitions on the original space and topology.

## Rational coefficients in the actual tangent basis

For the literal original rational multiplication p_k(x,y) and rational
identity coordinate c, define fixed rational polynomials

```
L_jk(x) = (partial_(second,j) p_k)(x,c),
C_ijk = (partial_i L_jk)(c) - (partial_j L_ik)(c).
```

The j-th actual left-invariant basis field at every original point g
has k-th coordinate L_jk(coord(g)). This follows by differentiating the
actual group law, using general analytic derivative formulas for
rational polynomial arrays. Coordinate lines are not assumed subgroups.
At the identity these fields have exactly their prescribed tangents.
Their actual Lie bracket coefficients are therefore C_ijk.

`original_tangent_basis_rational` states this through the repr of a basis
of the actual GroupLieAlgebra. The bracket types are specified explicitly
so that elaboration uses the original group's Lie bracket throughout.

## Same-basis full original H assembly

`original_full_rational_lie_basis_and_lattice` selects the compatible
full integer/real fiber bases once. Their rational original function
representatives give the actual H multiplication array and smooth Lie
structure in those same coordinates. The theorem supplies rational
coefficients of the actual tangent-basis bracket while retaining the
global time-one formula for all unrestricted v and Q, both rational
coordinate arrays, the correct origin and both entire original lattice
denominator inclusions. No separate existential basis choices are equated.

The denominator and rational structure coefficients precede all integer
vectors, original lattice elements and basis indices. The assertion is
for each fixed structural presentation. Uniform coefficient heights over
varying presentations are not inferred from rationality.

## Remaining exact interface

The actual Lie basis and bracket are now identified, and the generic
coordinate/native curve derivative bridge is proved. Next, assemble the
existing all-tangent subgroup existence and uniqueness with the global
time-one inverse into one theorem formulated using native Lie tangents,
retaining the same basis and witnesses. This is the remaining
exponential/logarithm identification interface.

Uniform heights, adapted Malcev and external metric/test/filtration/
interval matching, general structural descents and quantitative
termination, and original-frequency realization with all original labels,
circle roots, quadratic freedom, weights and full responses remain open.
These internal matching obligations are not external deep-theorem
exemptions. Final WeightedCapture/P0 remain open; P2-CSE and U0 remain
OPEN and the historical twelve invalid composite applications remain unused.

The new modules are OriginalChartDifferential, RationalCoordinateDifferential,
OriginalLeftInvariantCoordinates, OriginalChartLieBracket,
OriginalRationalLieBracket, OriginalFullRationalLieBasis,
LieConventionObstruction and OriginalCurveLieTangent.
