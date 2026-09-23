# Original rational inverses, Lie structure and denominator inclusions — F54

Checkpoint date: 2026-09-23. F54 adds 17 theorem declarations to F53's
1477, bringing the complete audited project to 1494 declarations.

P0 and WeightedCapture remain unproved. F54 continues the original rational
presentation from F53: inverse polynomials are derived, both group operations
are placed in a single original chart, and a smooth Lie structure is
constructed on the same group with the same topology. Separately, clearing
the denominators of specified rational coordinate maps is proved to give
both lattice inclusions with one positive integer.

## Scope checks

Two exact counterexamples protect the denominator step:

1. The rational affine image Z + 1/2 cannot contain any q*Z, since it
   misses zero. Rational forward and inverse coordinate formulas alone
   do not supply the lower inclusion; the origin condition matters.
2. The rational triangular map (x,y,z) -> (x,y,z+x*y/2) sends the integer
   grid to a set containing (1,0,0) and (0,1,0) but not their sum (1,1,0).
   A nonlinear rational coordinate image of a lattice need not be closed
   under ordinary vector addition.

Neither result is a counterexample to P0. The new inclusion proofs retain
the required origin condition and never use additive closure of log(Gamma).
The F53 scalar denominator obstruction also remains in force: fixed
dimension and degree alone do not bound the heights of varying rational
structural coefficients.

## Deriving the actual inverse

The base inputs remain the original coordinate equivalence, its literal
joint rational multiplication array p, and the original strictly triangular
left law with strict earlier-coordinate support. The original identity
coordinates are obtained as an integer vector from the actual Gamma;
they are not silently replaced by zero.

For each coordinate i, define a rational polynomial R_i recursively. In
the joint law p_i, retain the first coordinate vector X and substitute
the already constructed R_j into the second vector for j<i, setting all
other second coordinates to zero. Subtract this value from the i-th
original identity coordinate. Strong induction on i proves

```
R_i(coord(g)) = coord(g^-1)_i       for every original g.
```

The strict-prefix support implies that replacing later second coordinates
does not change the correction. The original identity g*g^-1=1 then gives
the induction step. No polynomial inverse formula is supplied as a premise.

Using F53's actual translation matrix T and the original convention

```
(g,F)^-1 = (g^-1, -F composed with L_(g^-1)),
```

the i-th inverse fiber coordinate is

```
-sum_j coefficient_j(F) * T_ij(coord(g^-1)).
```

Substitution of the derived R polynomials constructs the rational inverse
of the actual H. A combined theorem selects compatible original integer
and real bases, multiplication polynomials and inverse polynomials before
all H elements, and proves that the entire original H lattice is exactly
the integer grid in those same coordinates. No sublattice is substituted.

## Smooth structure on the original group

`rational_coordinate_lie_group` uses the original global coordinate
homeomorphism as its single chart. Rational polynomial evaluation is
proved smooth by polynomial induction. Literal joint multiplication and
inverse polynomials then prove both actual operations smooth in that chart,
constructing a Mathlib `LieGroup` of smoothness order infinity.

`original_observation_coordinate_lie_group` derives the needed polynomials
from the original rational base/basis data and strict triangular law, then
constructs this Lie structure on the actual ObservationGroup V. It does
not change the group multiplication, topology, observations or quotient.
The original coordinate homeomorphism also proves contractibility of the
underlying space.

This establishes a smooth Lie structure in the specified coordinate chart.
It does not yet identify its tangent algebra, the particular operators
D_X, or the actual Lie exponential and logarithm with the rational formulas
required by the manuscript. Nilpotence from the original bounded triangular
data is covered by the earlier explicit flag theorem; a complete assembled
quantitative Lie/Malcev presentation remains to be built.

## Clearing both directions, with exact quantifiers

For each fixed rational polynomial P, one positive integer a is chosen
before all integer vectors z such that

```
P(a*z) - P(0) is an integer.
```

If P(0) is an integer, this gives P(a*z) itself integral. The proof retains
the constant term and proceeds by polynomial induction. Finite products
of the coordinate denominators give one a for a whole finite polynomial
array. A separate positive integer b clears the output values of a fixed
rational polynomial array at every integer input.

Now fix rational polynomial arrays E and L, with L(E(x))=x for every real
x, and E(0) an integer vector. With q=a*b, the theorem proves

```
q*Z^d is contained in L(Z^k),
L(Z^k) is contained in q^-1*Z^d.
```

The same q is selected after E and L are fixed and before every integer
point in either inclusion. The proof sends q*z through E for the first
inclusion, and multiplies each L(w) by q for the second. It does not use
closure of L(Z^k) under addition.

`original_logarithmic_lattice_sandwich` applies this result to an actual
group H, its actual Gamma and original integer-coordinate equivalence,
and a specified logarithmic coordinate equivalence. Its hypotheses include
the literal rational formulas for both coordinate directions and
logCoord(1)=0. Its conclusion uses actual elements of Gamma in both
directions:

```
exists q>0,
  for every integer z, some original gamma has logCoord(gamma)=q*z;
  for every original gamma, q*logCoord(gamma) is an integer vector.
```

Thus the denominator argument itself is closed once the specified maps
are proved to be the intended rational Lie exponential and logarithm.
That identification remains open; a coordinate equivalence is not being
renamed the Lie logarithm without proof. Uniformity before arbitrary real
response data additionally requires selecting those coordinate formulas
from the fixed structural data, as the manuscript demands.

## Remaining interfaces

The next original-data obligation is to construct and identify the tangent
translation operators and actual H exponential/logarithm, with rational
formulas in the same structural coordinates. Their quantitative bounds
must then be connected to the permitted adapted Malcev basis results.
The new denominator theorem supplies the two inclusions after that map
identification; it is not the entire external weak-basis or quantitative
Leibman hypothesis package.

External metric/test/filtration/original interval-smoothness matching,
uniform bounds through general descents and termination, and original
frequency realization remain open. WeightedCapture must still be proved
with full labels, all circle roots, quadratic freedom and the unchanged
original responses and weights before applying the existing reduction to
P0. P2-CSE and U0 remain OPEN. The twelve invalid historical
three-dimensional composite applications remain DEFERRED and unused.

## Source and verification scope

The new source modules are RationalTriangularInverse,
RationalObservationInverse, RationalObservationOperations,
RationalPolynomialDenominators, RationalLatticeSandwich,
RationalLatticeObstructions and RationalCoordinateLieGroup. Their
declarations are included in the project root and transitive axiom audit.
The authoritative complete run is recorded in verification/result.json,
verification/build.log and verification/axioms.log. Machine checking proves
the stated theorems under their stated hypotheses; it does not establish
the still-open final P0 theorem.
