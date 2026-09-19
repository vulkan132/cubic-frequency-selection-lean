# Original rational observation presentation — F53

P0 and WeightedCapture remain unproved. F53 adds 19 theorem declarations
to F52's 1458. It derives rational observation translation and multiplication
polynomials from the original rational base law and function basis, constructs
compatible actual integer/real bases, and removes that basis premise from
the original full-orbit forcing theorem.

## Scope obstruction checked first

Rationality and bounded dimension or degree do not themselves imply a
uniform height bound. In the one-dimensional recovery problem

```
a * n = 1,        n a positive integer, a rational,
```

the reduced denominator of a is exactly n. The formal theorem
`rational_scalar_recovery_no_uniform_height` excludes a denominator bound
valid for all n. This is a constant-polynomial example with fixed dimension
and degree but varying structural coefficients. It is not a counterexample
to P0, whose constants may depend on its specified structural data.

Accordingly, the rational existence results below are not described as
uniform effective height bounds across changing presentations.

## From original points to a rational recovery matrix

The inputs are the original group G, actual observation module V, actual
subgroup Gamma, a real basis b whose functions have literal rational
coordinate polynomials P_j, and both directions of the original integer-grid
identification in the given base coordinates.

The whole integer grid separates coordinate polynomials, so evaluations on
the original Gamma separate every element of V. Finite-dimensionality then
selects at most dim(V) actual subgroup points u_k. Each point retains its
integer coordinate vector z_k; these are not arbitrary replacement points.

At those points, the basis evaluation matrix B has rational entries. Its
real columns are independent, and scalar restriction proves rational
independence. A rational linear left inverse yields one matrix A with

```
coefficient_i(F) = sum_k (A_ik : R) * F(u_k)   for every original real F.
```

The points, integer coordinate vectors and A are all selected before F and
its unrestricted real coefficients. The equality is proved for all F by
linear algebra, not inferred from finite empirical tests. Neither a
recovery matrix nor subgroup evaluation separation is a new final premise.

## Rational translation and the actual H multiplication

Assume the literal original joint coordinate group law has rational
polynomials p_s. For an original basis polynomial P_j, substitute
the coordinate pair (x,z_k) into p and then into P_j. This constructs a
rational polynomial in x whose value at coord(g) is exactly b_j(g*u_k).
Consequently

```
T_ij(coord(g)) = sum_k A_ik * b_j(g*u_k)
              = coefficient_i(b_j composed with L_g).
```

Thus the rational polynomial translation matrix T is a conclusion from
the original base law and basis functions. Subtracting the identity matrix
gives the actual difference matrix. Coordinate surjectivity and the existing
coefficient-span theorem now prove that the actual translation-difference
space W is rational in the original basis without supplying a translation
matrix as an extra assumption.

For H's actual multiplication convention

```
(g,F)*(h,Q) = (g*h, F composed with L_h + Q),
```

the i-th fiber coordinate is

```
coefficient_i(Q) + sum_j coefficient_j(F) * T_ij(coord(h)).
```

Together with the original base law, this supplies a single rational joint
polynomial array valid for every pair of original H elements. The second
base factor h, the original pullback order and every unrestricted real
fiber coefficient are retained.

## Constructed bases and the full original integer lattice

For any element F of the original integer-valued lattice V_Z, every F(u_k)
is an integer. The same rational recovery matrix therefore gives rational
coordinates for F in the supplied basis. Expanding in its literal rational
basis polynomials constructs an actual rational polynomial representative
for each F.

The previously proved existence of an integer basis for V_Z and its full
real span now construct a compatible real basis whose functions still have
rational polynomial representatives. No compatible basis is supplied as a
new input to this construction.

The theorem `observation_rational_group_full_lattice_presentation` selects
one d, integer basis bZ, compatible real basis bR and rational polynomial
array Q before all H elements. In those same base/fiber coordinates it
proves both the literal multiplication formula and

```
a belongs to the original Gamma_H
    iff all its full coordinates form one integer vector.
```

This identifies the entire original lattice, not a finite-index sublattice.
It does not assert that these coordinates are an adapted Malcev system or
that a quantitative weak-basis bound has already been established.

## The original full-orbit theorem with fewer premises

`original_rational_boundary_nonequidistribution` starts from the original
topological group with its Borel structure and discrete Gamma, the actual
coordinate homeomorphism, a rational joint base law, the strictly triangular
left law, the full integer grid, one original rational polynomial function
basis, constant one in V, and a fixed translated coordinate cell.

It constructs the compatible actual integer/real bases internally, then
uses F52 to construct the source and quotient metrics and cutoff geometry.
One original H quotient metric, with exactly the original quotient topology,
precedes every specified section in the fixed cell, invariant probabilities,
positive correlation threshold, finite orbit and N. For each such threshold
and specified section/probabilities, one t, alpha with 0<t<=1 and alpha>0
works for all full original finite orbits. The original sum divided by N
is retained; under card(I)<=N, correlation greater than gamma implies
gamma*N<card(I) and the same discrepancy failure. No original point is
discarded or observation replaced.

The joint rational base law and the strict triangular law remain distinct
explicit inputs. They have not been silently identified or derived from
an unspecified abstract Lie presentation.

## Remaining core interfaces

The rational translation matrix, rational H joint law, rationality of W,
compatible rational integer basis and actual full-lattice integer coordinates
are now derived. Still required are:

- full original Lie/exponential and adapted Malcev structure, with the
  quantitative rational complexity and heights needed in the argument;
- matching the constructed metrics, original tests, actual filtration and
  original interval smoothness norm to the permitted external quantitative
  theorem;
- general descent constructions, their tracked quantitative data and
  termination, then original-frequency extraction and realization;
- final weighted finite capture in the original full-label d_(3,N) metric,
  retaining all circle roots, quadratic freedom, original weights and
  responses, followed by the proved conditional reduction to P0.

These internal obligations are not reclassified as external deep theorems.
P2-CSE and U0 remain OPEN. The twelve historical invalid three-dimensional
composite applications remain DEFERRED and unused.

## Verification evidence

The seven new source modules are RationalEvaluationRecovery,
RationalObservationTranslation, RationalObservationGroup,
ObservationIntegerRationalBasis, RationalOriginalOrbit,
RationalRecoveryHeightObstruction and RationalObservationLatticeCoordinates.
All nineteen theorem declarations are exported and included in the full
transitive axiom audit. The whole-project run is recorded in
verification/result.json and its build/axiom logs. Passing checks establish
these stated theorems under their stated premises; neither their count nor
file hashes establish the open P0 conclusion.
