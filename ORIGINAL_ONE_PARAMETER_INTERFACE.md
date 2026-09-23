# Original one-parameter translation and observation lift — F56

Checkpoint date: 2026-09-23. F56 adds 24 theorem declarations to F55's
1518, bringing the project to 1542. P0 and WeightedCapture remain unproved.
The work connects F55's actual differential and finite fiber polynomial
to the manuscript's original semidirect multiplication, rather than
assuming that the finite expression is an exponential map.

## Scope check before the positive argument

For translations of the real line and Q(u)=u, the naive fiber t*Q would
require (s+t)u=s(t+u)+tu. The exact values s=t=1,u=0 contradict this.
The corrected fiber tu+t^2/2 satisfies

```
(s+t)u + (s+t)^2/2 = s(t+u) + s^2/2 + tu + t^2/2
```

identically. Both statements are checked. This protects the higher fiber
terms and the original pullback order. Neither is a P0 counterexample.

## Exact integration of the original derivative tower

`finite_derivative_tower_exact` treats arbitrary real functions f_j with
actual derivative f_(j+1) and f_K identically zero. It proves, at every
real time t,

```
f_0(t) = sum_{j<K} t^j/j! * f_j(0).
```

The proof differentiates the factorial monomials, retains the actual
initial values and uses uniqueness from equal derivatives and one equal
initial value. It is a general proof with no finite testing or remainder
estimate. Height zero is included without replacing any initial data.

Fix an actual original base path gamma satisfying
gamma(s+t)=gamma(s)*gamma(t) for all real s,t. Its value gamma(0)=1 follows
from this law. Suppose its original coordinate derivative at zero is v.
F55 supplies the actual operator D(v), with a common exponent K and the
pointwise derivative of every original function at zero. The group law
propagates that derivative to all real times in the original order:

```
d/dt F(gamma(t)*u) = (D(v)F)(gamma(t)*u).
```

Apply the derivative-tower theorem to the actual functions
f_j(t)=(D(v)^j F)(gamma(t)*u). The top function vanishes because D(v)^K=0.
The result is the endomorphism identity

```
T_gamma(t) = sum_{j<K} t^j/j! * D(v)^j
```

on the entire original observation space, for every real t. No original
function, coefficient or evaluation response is replaced.

## The actual fiber path and original group law

Define the original-space endomorphism

```
S(t) = sum_{j<K} t^(j+1)/(j+1)! * D(v)^j.
```

It has zero initial value and its pointwise derivative on every original
Q is exactly T_gamma(t)Q. Comparing actual derivatives and initial values
at all original evaluation points proves

```
S(s+t)Q = T_gamma(t)(S(s)Q) + S(t)Q.
```

Consequently eta(t)=(gamma(t),S(t)Q) has eta(0)=1 and
eta(s+t)=eta(s)*eta(t) in the original H, whose multiplication is
(g,P)*(h,Q)=(g*h,P composed with L_h+Q). This is an exact group-law
identity, not a declaration of a new group law on the same set.

Every original pointwise vertical derivative at zero is Q(u). Exact
finite recovery of basis coefficients carries those pointwise derivatives
back to the actual original basis coefficients. In the full original
coordinate homeomorphism of H, the derivative at zero is precisely
Sum.elim(v,basisCoordinates(Q)). The original identity coordinate is kept;
the proof does not reset it to zero.

## Uniqueness and the time-one formula

Any other actual H path satisfying the same parameter group law, the same
entire base path gamma, and pointwise vertical derivative Q at zero has
fiber derivative Q(gamma(t)*u) at every real time. Its fiber initial value
is zero by the group law. Actual scalar initial-value uniqueness therefore
proves equality with eta at every real parameter and every original point.

At time one, S(1)=Phi_K(D(v)), where Phi_K is exactly the F55 polynomial.
The extra j=K term used in that definition vanishes by D(v)^K=0. Thus the
time-one value has the manuscript's precise factorial coefficients and
retains the same fixed rational polynomial inverse from F55.

## Final quantifier order and original-data assembly

`original_integral_basis_one_parameter_lift` starts with the same literal
original rational joint law, strict triangular corrections, original
coordinate homeomorphism, full integer grid and rational function basis.
It constructs a basis of the entire original integer-valued lattice and
its compatible real basis, rational basis representatives, the rational
differential tensor, one positive K and the two rational fiber polynomials.

All these choices precede every base path gamma, every real tangent v,
and every unrestricted original Q. For each gamma satisfying the actual
group law and indicated original coordinate derivative, the theorem gives
the full translation series, H identity and group law, complete coordinate
tangent, rational time-one fiber and uniqueness over that same base path.
The inverse polynomial identities hold for every real tangent in the same
constructed basis. There is no differential, nilpotence, lift, or
exponential-formula premise hidden in the statement.

The quantifier is explicitly **for every path satisfying these conditions**.
It is not an assertion that such a base path exists for every v. Uniqueness
over a fixed base path does not assert uniqueness of base paths from their
initial tangent. These are separate remaining obligations.

## Remaining interfaces

Construct and identify the original base one-parameter subgroups for
every tangent, connect their coordinate tangents to the intended rational
Lie basis and the actual base exponential, and establish the global
rational exponential and logarithm with their inverse identities. The
current result proves the actual H lift law and conditional uniqueness;
it does not yet supply a globally defined Lie exponential/logarithm or
their complete smooth/global identification.

After those maps are identified, F54's original-lattice denominator result
can be used for the intended logarithmic inclusions. Uniform structural
heights, adapted Malcev and external quantitative metric/test/filtration/
original-interval matching remain open. General descents and quantitative
termination, original-frequency realization with all labels, circle roots,
quadratic freedom, original weights and responses, and final
WeightedCapture/P0 remain open. P2-CSE and U0 stay OPEN. The historical
twelve invalid three-dimensional composite applications stay DEFERRED
and unused.

## Verification scope

The new modules are OneParameterObstruction, FiniteDerivativeTower,
OneParameterTranslation, OneParameterFiber, ObservationOneParameter and
OriginalOneParameterLift. All new theorems are imported by the project
root and included in the transitive axiom audit. The complete
`python verify.py` run is recorded in verification/result.json,
verification/build.log and verification/axioms.log. Machine checking
establishes these exact statements under their exact hypotheses, not the
still-open final P0 theorem.
