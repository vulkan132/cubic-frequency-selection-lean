# Original conjugation and native lower-central invariance — F65

F65 adds 18 theorem declarations to F64's 1676. The full build and
transitive axiom audit are recorded in verification/result.json,
build.log and axioms.log. P0 and WeightedCapture remain unproved.

## The actual conjugation differential

For the original chart c and original group element g, define

```
C_g(x) = c(g * c^(-1)(x) * g^(-1)),
A_g = D C_g(c(1)).
```

Smoothness of the original group operations proves differentiability at
the original identity. A two-way native/coordinate differential lemma
identifies A_g with the actual manifold differential of conjugation.
The identity coordinate is c(1), not an assumed zero vector.

If gamma is an actual native one-parameter subgroup with tangent v,
then g*gamma(t)*g^(-1) is an actual native subgroup with tangent A_g(v).
The proof retains both actual differentiability and the group law.
Uniqueness from the same original weak-basis witnesses therefore gives

```
Exp(A_g(v)) = g * Exp(v) * g^(-1),
Log(g*h*g^(-1)) = A_g(Log(h)).
```

These hold for all original g,h and all unrestricted original v. The
global exponential equivalence also proves A_1=id and A_(g*h)=A_g o A_h,
in exactly the original multiplication order. No coordinate coefficient
bound uniform over arbitrary g is asserted.

## The actual native Lie bracket

The inverse differential of conjugation at h is the differential of
inverse conjugation at g*h*g^(-1). This follows by differentiating the
two exact inverse-composition identities. Function and basepoint
congruence lemmas explicitly transport the native tangent spaces.

Pulling back the actual left-invariant field of v by conjugation with g
then gives the left-invariant field of A_(g^(-1))(v). This is proved by
differentiating the actual group identity between conjugation composed
with left translation and left translation composed with conjugation.

Mathlib's proved naturality theorem for vector-field Lie brackets under
pullback yields

```
A_g([v,w]) = [A_g(v), A_g(w)].
```

Both brackets are explicitly the native GroupLieAlgebra brackets; the
coordinate-function pointwise bracket is not used. The resulting native
Lie homomorphism originalAdjointLieHom is constructed from this proof.
Bracket compatibility is neither an assumption nor an external premise.

## Actual lower-central invariance and original witnesses

The actual Lie-ideal map theorem now proves A_g(I_n) is contained in I_n
for every original g and every native lower-central layer I_n. Applying
the exponential/logarithm identities and inverse conjugation gives

```
g*h*g^(-1) belongs to Exp(I_n)  iff  h belongs to Exp(I_n).
```

This is stability of the actual exponential set under every original
group conjugation. The argument uses the characteristic nature of the
lower-central series; it does not claim all arbitrary Lie ideals are
preserved by every Lie automorphism.

original_lower_central_conjugation_data combines this with all F64
closedness, contractibility, inverse/power and original-lattice logarithmic
span data using the same original weak basis and rational arrays.
original_full_conjugation_lie_filtration retains the full original
integer/real bases, entire original lattice, smooth exponential/logarithm,
all original weak-basis and array bounds, actual Lie-layer rationality and
finite-depth bounded bases from one structural construction. No original
function, weight, response, circle branch or quadratic freedom is changed.

## Remaining integration and P0 interfaces

Conjugation-invariant sets are not yet proved to be subgroups. The next
core obligation is multiplicative closure of the relevant exponential
images, followed by the original group/Lie lower-central correspondence
and the required commutator relations with correct index conventions.
Original lattice-intersection cocompactness, common adapted Malcev data
and quantitative external metric/test/interval matching remain open.

Controlled general descent families and quantitative termination,
original full-label frequency realization, and WeightedCapture/P0 remain
open. No external deep theorem or project axiom has been added. P2-CSE
and U0 remain open; the historical twelve invalid three-dimensional
composite applications remain deferred and unused.
