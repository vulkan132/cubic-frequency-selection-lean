# Original subgroups for all coordinate tangents — F57

Historical checkpoint. F58 constructs the rational base logarithm, both
base inverse identities, base-lattice inclusions and the full H global
time-one inverse in ORIGINAL_GLOBAL_LOG_INTERFACE.md. STATUS.md is current.

Checkpoint date: 2026-09-23. F57 adds 25 theorem declarations to F56's
1542, bringing the audited project to 1567. P0 and WeightedCapture remain
unproved. The new result discharges F56's missing base-path existence
and strengthens its uniqueness statement to every full original tangent.

## Scope check and exact input

The F55 and F56 obstructions still apply: a rational curve with the
identity value need not satisfy a group law, and the naive fiber tQ
fails even for affine observations. We do not declare the coordinate
line through the identity to be a subgroup. It is used only to compute
an actual derivative at the actual identity.

Inputs are the same original coordinate equivalence (a homeomorphism
in the full assembly), literal rational joint group law, and the original
strict triangular left-translation law. The full H assembly also uses
the original observation module, full integer grid and rational function
basis. No base subgroup, subgroup existence theorem, or exponential
formula is supplied. All statements hold in arbitrary finite dimension,
including zero, and retain a possibly nonzero original identity coordinate.

## Original velocity and strict triangular dependence

Write c for the original identity coordinate, and p_i(x,y) for the
original rational multiplication polynomials. Define

```
F_v(y)_i = sum_j (partial_(first j) p_i)(c,y) * v_j.
```

This is the actual derivative of left multiplication by a coordinate
curve through the identity with tangent v. The derivative theorem holds
for every actual original right translate of every differentiable
coordinate curve, with every original evaluation retained.

The identity law gives F_v(c)=v. Differentiating original associativity
gives its right-translation covariance at every original pair (g,u).
Differentiating the actual strict triangular law proves that F_v(y)_i
depends only on the coordinates y_j with j<i. This restriction is on y,
not on v: every tangent component is retained. The fixed rational
polynomial array `originalVelocityPolynomial` represents the same F
simultaneously for all real v and y.

## Exact construction for all tangents

`polynomialTimePrimitive` integrates a polynomial coefficientwise over
any rational algebra. Its derivative is exactly the original polynomial,
and its initial value is zero. Specialization of the coefficients to
real numbers preserves the actual analytic derivative at every real time.

The coefficient algebra is Q[v_0,...,v_(m-1)]. In strict coordinate order,
construct a polynomial C_i(v,t) whose constant term is c_i and whose
time derivative is the fixed velocity polynomial evaluated on the
already constructed lower-coordinate polynomials. Higher coordinates
may be set to zero at this substitution step because the actual velocity
has the proved prefix dependence. No tangent coordinates are set to zero.

Thus one fixed array in (Q[v])[t], selected before every real v and t,
satisfies

```
C(v,0) = c,
d/dt C(v,t) = F_v(C(v,t))
```

at every real time. The original group path is
gamma_v(t)=coord.inverse(C(v,t)). It has gamma_v(0)=1 and the original
coordinate derivative v at zero. No bounded-tangent hypothesis occurs.

## Actual group law, uniqueness and time scaling

Global uniqueness for the triangular differential equation is proved
coordinate by coordinate. Once all earlier coordinates agree, the next
two scalar functions have equal derivatives everywhere and equal actual
initial values, and hence agree at every real time.

For each fixed t, the paths gamma_v(s+t) and gamma_v(s)*gamma_v(t)
solve the same equation by the proved right-translation covariance.
Their original initial values agree, so

```
gamma_v(s+t) = gamma_v(s) * gamma_v(t)
```

for all real s,t. This is the original group multiplication. Conversely,
every original subgroup path with initial coordinate tangent v satisfies
the same equation, by translating its actual derivative at zero using
its group law. It therefore equals gamma_v at every real time.

The same uniqueness proves gamma_(a v)(t)=gamma_v(a t) for every real
a,v,t, including zero and negative a. Setting t=1 in the constructed
polynomial array gives fixed rational polynomials for coord(gamma_v(1))
in every component of v. This is an actual subgroup value, not a supplied
exponential formula.

## The complete original observation group

A full coordinate derivative in H supplies the actual base derivative
and, by the exact original basis evaluation formula, the derivative of
every unchanged original fiber value. F56's lift can now be used over
the constructed gamma_v for each v and every unrestricted original Q:

```
eta_(v,Q)(t) = (gamma_v(t), sum_(j<K) t^(j+1) D(v)^j Q/(j+1)!).
```

The actual H identity, real parameter group law, full coordinate tangent,
translation finite series and rational time-one fiber all follow from
the already checked F56 results. If another actual H subgroup has the
same full initial tangent, its base equals gamma_v by the new base
uniqueness theorem. F56's original fiber uniqueness then identifies the
entire path. Agreement of entire base paths is now a conclusion, not an
additional hypothesis.

The final theorem `original_integral_basis_full_one_parameter` first
constructs the original rational identity coordinate, full integer/real
compatible bases, rational basis representatives, differential tensor,
one positive nilpotency exponent and the fixed rational fiber polynomial
and inverse. All those choices precede every v and every original Q.
The full original lattice is retained; no sublattice or replacement
observation space is introduced.

## Remaining mathematical interfaces

The actual unique subgroup for every coordinate tangent and its time-one
base polynomial are now proved. The formal correspondence of this
coordinate tangent basis and time-one map with the intended rational
Lie basis and exponential still requires matching. Global bijectivity
of the time-one map and a literal rational logarithmic inverse, with
both inverse identities, are not asserted. Unique subgroups for given
tangents alone do not establish the full global logarithm theorem.

After that correspondence and the inverse identities are proved, F54's
original-lattice denominator theorem can be applied to the intended
logarithmic inclusions. Uniform rational heights, adapted Malcev and
external quantitative metric/test/filtration/original-interval matching,
general descents and quantitative termination, original-frequency
realization in the full-label metric with all circle roots, quadratic
freedom, original weights and responses, and final WeightedCapture/P0
remain open. P2-CSE and U0 remain OPEN. The twelve invalid historical
three-dimensional composite applications remain DEFERRED and unused.
No internal obligation has been renamed an external deep theorem.

## Verification

The six new modules are PolynomialTimePrimitive,
TriangularDifferentialUniqueness, OriginalCoordinateVelocity,
RationalTriangularFlow, OriginalBaseOneParameter and
OriginalFullOneParameter. Every new theorem is imported by the root
and printed in the transitive axiom audit. `python verify.py` builds
the full project and compares every theorem with the allowed standard
foundations. Its records are verification/result.json, build.log and
axioms.log. These checks establish the exact conditional statements;
they do not establish the still-open final P0 theorem.
