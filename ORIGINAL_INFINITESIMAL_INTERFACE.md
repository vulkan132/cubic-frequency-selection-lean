# Original infinitesimal translation and finite fiber inverse — F55

Historical checkpoint. F56 connects the finite series to the actual
subgroup-path law in ORIGINAL_ONE_PARAMETER_INTERFACE.md. STATUS.md records
the current scope.

Checkpoint date: 2026-09-23. F55 adds 24 theorem declarations to F54's
1494, bringing the audited project to 1518. P0 and WeightedCapture remain
unproved. The new work targets the infinitesimal calculation preceding
the manuscript's observation-group exponential formula in
`sections/04-freezing.tex`, rather than assuming that formula.

## Scope obstruction

The rational scalar polynomial T(t)=1+t equals the identity at t=0, but
T(s+t)=T(t)T(s) fails at s=t=1: its two sides are 3 and 4. This exact
counterexample is checked in Lean. A rational polynomial matrix and its
identity value do not alone make a translation representation or identify
a Lie exponential. The positive results below use the actual original
translation operators and preserve their original multiplication order.
This obstruction is not a counterexample to P0.

## Uniform degrees from the original fixed data

`polynomial_substitution_totalDegree_le` proves that substituting
degree-at-most-D polynomials into P gives degree at most deg(P)*D.
Specializing the first vector in the fixed original joint group law
therefore bounds its degree uniformly over every translating point.

Surjectivity of the original coordinates identifies the actual triangular
correction polynomial with this specialization minus the current variable.
The identification uses equality on all real coordinate inputs, not a
finite test. Taking the maximum over the fixed finite coordinate array
gives one D before all original group elements.

Every original observation is an unrestricted real linear combination of
the fixed rational polynomial basis. The same linear combination of its
polynomial representatives has degree at most their fixed finite maximum
R. Thus R precedes every real observation, without any coefficient bound.

The earlier triangular construction now yields a common original flag
with height K=R*(D+1)^m+1, with zero bottom, full top, and strict lowering
by every actual translation difference. No flag or global degree premise
is supplied. Together with the original base nilpotence assumption, this
also gives H nilpotent of class at most class(G)+K; the F54 actual global
chart supplies its smooth Lie structure and contractibility.

## The actual coordinate differential

Let T_ij be the rational polynomial matrix of original translations,
derived at F53, and let c be the original identity coordinate. The latter
is rational because the actual original identity lies in the original
integer-coordinate lattice. Its value is retained; it is not assumed zero.
Define the fixed rational tensor

```
A_ijs = (partial_s T_ij)(c).
```

For a real coordinate tangent v, the endomorphism D(v) of the original
observation space has matrix entries sum_s A_ijs*v_s in the original
basis. Its additivity and homogeneity in v are proved, and it is a genuine
linear endomorphism in the original observation argument.

Polynomial induction connects formal rational partial derivatives to
analytic derivatives. For every original curve gamma with gamma(0)=1
and coordinate derivative v, every original F and every original u,

```
d/dt at 0 of F(gamma(t)*u) = (D(v) F)(u).
```

All original coefficient derivatives are proved as well. These are actual
function identities for arbitrary unrestricted real F. They do not replace
the original function with an evaluated response or a newly selected one.

This theorem applies to all differentiable curves with the indicated
coordinate tangent. It does not assert that the coordinate straight line
is a one-parameter subgroup, nor identify a supplied curve as exp_G(tX).
The correspondence with the intended rational Lie basis remains explicit.

## A common nilpotency exponent

For F in flag(n+1), all actual differences T_g F-F lie in flag(n).
Use the actual curve obtained from c+t*v by the original coordinate inverse.
Its difference quotients remain in the same lower original subspace.
Map that subspace into the finite-dimensional original basis coordinates;
its closedness passes membership to the proved derivative. Consequently
D(v) strictly lowers the original flag for every real v.

Induction on the flag level proves

```
exists K>0, for every real v, D(v)^K = 0
```

as an equality of endomorphisms of the entire original observation space.
The same K precedes all v, all original functions and all evaluation points.
Neither the differential matrix nor its nilpotence is an input premise.

## The finite fiber sum and its rational inverse

In any possibly noncommutative rational algebra, put

```
Phi_K(D) = sum_{j=0}^K D^j/(j+1)!.
```

If D^K=0, its last term vanishes; retaining that term simplifies the
uniform formula and also handles degenerate zero spaces. The identity
term is kept. Direct finite-sum algebra gives Phi_K(D)=1+D*Q_K(D), where
Q_K is a fixed rational polynomial. It commutes with D, so
(1-Phi_K(D))^K=0. The bounded geometric sum

```
Psi_K(D) = sum_{j=0}^{K-1} (1-Phi_K(D))^j
```

satisfies Psi_K(D)*Phi_K(D)=1 and Phi_K(D)*Psi_K(D)=1. Both Phi_K and
Psi_K are identified with evaluations of fixed rational polynomials
chosen before every D with D^K=0. This is an exact proof, including the
noncommutative endomorphism algebra, not a finite matrix test.

The final theorem `original_integral_basis_infinitesimal_fiber` constructs
a basis of the entire original integer-valued function lattice, its
compatible real basis and rational basis representatives, then derives
the rational tensor, common exponent and the two rational polynomials in
that same basis. All choices precede every real tangent, curve, original
observation and evaluation point. No lattice is replaced by a sublattice.

## Remaining interfaces

The actual infinitesimal calculation and finite inverse are now proved
in original coordinate tangents. Still needed are identification with the
intended rational Lie-basis tangents and construction/identification of
the actual one-parameter subgroups, showing that the manuscript's pair
(exp_G X, Phi_K(D_X)Q) is the actual exp_H(X,Q). The original base
exponential and logarithm and the global rational formulas in the same
coordinates also require matching. The polynomial inverse theorem alone
does not supply those identities or a global Lie logarithm.

Only after these identities are supplied can F54's original-lattice
denominator theorem be applied as the intended logarithmic statement.
Uniform structural heights, adapted Malcev and external quantitative
metric/test/filtration/original-interval matching remain open. General
descents and quantitative termination, original-frequency realization
with full labels, all circle roots, quadratic freedom, original weights
and responses, and final WeightedCapture/P0 also remain open. P2-CSE and
U0 stay OPEN. The twelve invalid historical three-dimensional composite
applications remain DEFERRED and unused.

## Verification

The seven new modules are PolynomialPresentationBounds,
RationalPolynomialDerivative, RationalObservationFlag,
ObservationInfinitesimal, InfinitesimalNilpotent,
NilpotentFiberPolynomial and OriginalInfinitesimalFiber. Every new theorem
is imported by the root and listed in the transitive axiom audit.
`python verify.py` builds the project and checks every theorem against
the standard-foundation whitelist. The run is recorded in
verification/result.json, verification/build.log and verification/axioms.log.
These checks establish the stated theorems under their stated hypotheses;
they do not prove the still-open final P0 theorem.
