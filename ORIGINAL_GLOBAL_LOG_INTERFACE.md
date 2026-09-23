# Original global time-one inverse and rational base logarithm — F58

Checkpoint date: 2026-09-23. F58 adds 25 theorem declarations to F57's
1567, bringing the project to 1592. P0 and WeightedCapture remain unproved.
The new work constructs the missing global inverse from actual original
powers, rather than supplying a logarithmic map as a premise.

## Scope and the endpoint issue

F57's uniqueness of a subgroup with a prescribed initial tangent does not
alone prove injectivity of its time-one value. The new proof explicitly
uses the actual original polynomial coordinates: equal time-one values
give equal natural powers, hence equality at every natural time. Two real
polynomials agreeing at every natural number are identical, by the general
infinite-root theorem. Therefore the paths agree at every real time and
their actual initial coordinate derivatives agree.

This is a theorem on the entire natural grid, not a finite test. The
inputs remain the literal original rational joint multiplication, strict
triangular law, coordinate equivalence and rational identity coordinate.
No endpoint inverse, surjectivity or global logarithm is supplied.

## Exact rational discrete integration

For each n, the rational Bernoulli polynomial provides

```
d_n(t) = (B_(n+1)(t) - B_(n+1)(0))/(n+1),
d_n(0) = 0,    d_n(t+1)-d_n(t) = t^n.
```

These are exact polynomial identities, using the checked Mathlib
Bernoulli identity. Extending coefficientwise over any rational algebra
gives an operator I with I(P)(0)=0 and forward difference P. Every real
specialization preserves the same identity at every real time.

The coefficient algebra is Q[x_0,...,x_(m-1)], retaining every original
element coordinate. In strict coordinate order, integrate the original
joint multiplication polynomial with the already constructed earlier
power coordinates substituted into its second input. Its current and
later second-input coordinates are zero at this substitution stage;
the actual strict triangular law justifies that exact correction. The
constant term is the unchanged original identity coordinate c_i.

This constructs one fixed array P_i(x,t) in (Q[x])[t]. Induction on n
using the actual original group multiplication proves

```
P(coord(g),n) = coord(g^n)
```

for every original g and every natural n, including zero. Neither the
element coordinates nor the natural exponent are bounded.

## Full real subgroup law and the actual logarithm

Define the original power path eta_g(t)=coord.inverse(P(coord(g),t)).
Its coordinates are real polynomials after the original g is fixed.
First fix a natural left parameter and extend the original power identity
in the other parameter by polynomial identity. Then fix that arbitrary
real parameter and extend in the first parameter. This proves

```
eta_g(s+t) = eta_g(s)*eta_g(t)
```

for every pair of real s,t, in the original group law. In particular
eta_g(1)=g. The rational array L_i(x)=[t^1]P_i(x,t) gives the actual initial
coordinate derivative of eta_g. Define Log_G(g)=L(coord(g)).

F57's uniqueness of the original subgroup with that tangent identifies
eta_g with gamma_(Log_G(g)). Consequently

```
gamma_(Log_G(g))(1) = g.
```

The independently proved endpoint injectivity then gives

```
Log_G(gamma_v(1)) = v
```

for every unrestricted real v. The same fixed forward and inverse rational
arrays therefore form a global equivalence. Its zero tangent maps to the
actual identity, and F57's time-scaling identity is retained at every real
time. The original identity coordinate need not be zero.

## The original base lattice

With the original full integer grid for Gamma, its identity gives the
required rational c. The constructed equivalence, literal rational arrays
and correct origin now discharge F54's coordinate-map hypotheses for the
base group. One positive k precedes every integer vector and lattice point:

```
k Z^m  is contained in Log_G(Gamma),
k Log_G(Gamma) is contained in Z^m.
```

The proof keeps the same original Gamma and does not assume that its
logarithmic image is additive. This closes the actual base-coordinate
denominator application, not yet the full H coordinate-array application.

## The actual full observation-group inverse

F57 constructs the full original integer/real compatible bases, original
observations, rational differential tensor, common nilpotency exponent,
and the same rational fiber polynomials Phi and Psi in both inverse orders.
The base equivalence above now gives an actual global equivalence

```
(v,Q) -> (gamma_v(1), Phi(D(v))Q),
(g,P) -> (Log_G(g), Psi(D(Log_G(g)))P).
```

Both inverse identities hold on the full original observation space.
The forward value is proved equal to the actual F57 subgroup's time-one
value, and the zero tangent pair maps to the original H identity. All
bases, tensors and polynomials precede all real v, all unrestricted
original Q, and all original H elements. No original function or lattice
is replaced, and no new inverse premise is introduced.

The logarithms here are on the original groups G and H. They are not maps
on the nilmanifold quotients and do not choose or discard circle-frequency
root branches.

## Remaining interfaces

The next algebraic assembly is to express both full H coordinate maps
as literal multivariate rational polynomial arrays in the same original
integer/real basis, including the composed base logarithm in the inverse
fiber, and apply the full H logarithmic lattice theorem. The global H
bijection itself is now proved; this coordinate/denominator assembly
is not asserted by a type name or by the base-only lattice theorem.

The formal matching of the coordinate tangent basis and constructed maps
to the intended rational Lie basis and standard exponential/logarithm
remains. Uniform rational heights, adapted Malcev and external quantitative
metric/test/filtration/original-interval matching, general descents and
quantitative termination, original-frequency realization with full labels,
all circle roots, quadratic freedom, original weights and responses, and
final WeightedCapture/P0 remain open. P2-CSE and U0 remain OPEN. The twelve
invalid historical three-dimensional composite applications remain
DEFERRED and unused. No internal obligation is reclassified as an external
deep theorem.

## Verification

The eight new modules are PolynomialNaturalIdentity, OriginalBaseEndpoint,
PolynomialDiscretePrimitive, PolynomialSubgroupExtension,
RationalOriginalPowers, OriginalBaseLogarithm, OriginalBaseLogLattice and
ObservationTimeOneInverse. All new theorems are imported by the root and
included in the transitive axiom audit. `python verify.py` checks the full
project and its allowed standard foundations; verification/result.json,
build.log and axioms.log record the run. This verifies the exact conditional
statements, not the still-open final P0 theorem.
