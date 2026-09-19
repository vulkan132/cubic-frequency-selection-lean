# Actual observation polynomials and full original orbit forcing — F52

Historical checkpoint. F53 derives rational translation and H laws and
compatible rational integer bases from the original data; the current
scope is RATIONAL_OBSERVATION_PRESENTATION_INTERFACE.md.

P0 and WeightedCapture remain unproved. F52 adds 10 theorem declarations
to F51's 1448. It derives the actual observation-group polynomial law and
constructs its source metrics and base/fiber regularity, then assembles
the original boundary forcing result without supplied metric assumptions.

## Exact inputs and quantifiers

The final theorem is `original_polynomial_boundary_nonequidistribution`
in `GMZP0/PolynomialOriginalOrbit.lean`. Its inputs are:

- the actual topological group G, observation module V and discrete original
  subgroup Gamma, with the original Borel measurable structure;
- the original coordinate homeomorphism G -> R^m, its literal joint
  polynomial multiplication law, and its strictly triangular left
  multiplication law with strict earlier-coordinate support;
- both directions of the original integer-grid identification;
- compatible bases of the actual integer-valued observation lattice over
  Z and V over R, and literal coordinate polynomials for those basis functions;
- the constant-one function in V and a fixed translate of the coordinate cell.

The joint base law and the triangular law are distinct explicit premises.
The proof does not infer a joint polynomial law from polynomial dependence
on only the second group variable. It does not infer rationality or bounded
heights from a real polynomial presentation.

It constructs a metric on the original quotient H/Gamma_H with exactly the
original quotient topology. This metric is selected before every specified
original section c whose range lies in the fixed cell, both specified
invariant probabilities mu and nu, the threshold gamma > 0, and all finite
orbits and lengths N. For each such c, probabilities and gamma, one pair
t, alpha with 0 < t <= 1 and alpha > 0 works simultaneously for:

1. Every finite index type I and every original quotient orbit u: a full
   original observation mean of norm greater than gamma excludes the
   stated Lipschitz orbit discrepancy bound at alpha.
2. Every N > 0, every finite I with card(I) <= N, and every u: a sum of the
   same original observations divided by the original N, of norm greater
   than gamma, implies gamma*N < card(I) and the same discrepancy failure.

No index point is removed and the original denominator is unchanged. This
is a boundary forcing theorem, not yet the external quantitative Leibman
conclusion or the final finite original-frequency capture theorem.

## Deriving the actual H law

Finite-dimensionality and separation of actual functions on the entire
original group give actual points u_k, with their number at most dim(V),
and a fixed real matrix A such that

```
coefficient_i(F) = sum_k A_ik * F(u_k)       for every F in V.
```

This is a universally proved linear identity. The finite evaluations are
not empirical tests of a general mathematical claim. They are chosen
before all unrestricted original real observation coefficients.

Write the original basis functions as B_j and F = sum_j c_j B_j. For the
actual multiplication convention

```
(g,F) * (h,Q) = (g*h, F composed with L_h + Q),
```

the i-th fiber coordinate is exactly

```
coefficient_i(Q) + sum_k sum_j A_ik * c_j * B_j(h*u_k).
```

The original joint polynomial law on G and the given polynomials for B_j
make this a joint polynomial in the actual coordinates of both H factors.
This proves H's polynomial presentation internally and retains the order
h*u_k. No translation matrix or alternative H multiplication is supplied.

The actual H coordinate homeomorphism consists of the original base
coordinates and the original basis coefficients. Applying F51's metric
construction to G and this derived H presentation constructs both source
metrics, all right-translation isometries, and local Lipschitz regularity
of the G coordinates and inverse. Coordinate restrictions are 1-Lipschitz;
composition proves local Lipschitz regularity of the actual H base map
and actual fiber-coordinate map.

## What the assembled proof derives

The proof internally uses the original strict-cell correction and compact
cover, proves the actual observation lattice closed from all its integer
evaluation conditions, and constructs both original quotient metrics.
It then invokes the proved geometric chain for original pair lifts, short
paths, projection bounds, boundary tube mass, cutoff regularity, original
probability projection and zero mean. The resulting full orbit statement
uses the unchanged original quotient observation.

The new evaluation matrix is real and noncomputably chosen. The supplied
basis polynomials and joint group polynomials in these results have real
coefficients. These facts suffice for the metric construction but do not
supply uniform rational presentations, rational coefficient heights or
effective complexity bounds across changing structural data. The earlier
bounded-metric obstruction continues to exclude a global comparison with
unbounded source coordinates; the proved comparisons are local or on fixed
compact sets.

## Remaining obligations

The core interfaces still needing closure are:

1. Match the literal base presentations and compatible lattice basis to
   the complete original rational Malcev/Lie data with the required uniform
   rational complexity and heights. Match the constructed quotient metric,
   test functions, filtration and original interval smoothness norm to the
   permitted external quantitative theorem. Fixed-presentation compactness
   and real polynomial existence alone do not give these uniform bounds.
2. Prove the general descent steps and a well-founded termination argument
   with constants tracked through every step.
3. Extract and realize a uniformly finite list of original frequencies,
   retaining the original full-label d_(3,N) distance, all required circle
   roots, quadratic freedom, original responses and weights. Prove
   WeightedCapture and apply the existing conditional reduction to P0.

External deep theorem proofs may remain explicit permitted inputs. The
internal matching, height, descent and realization obligations above are
not reclassified as external assumptions. P2-CSE and U0 remain OPEN. The
historical twelve invalid three-dimensional composite applications remain
DEFERRED and unused.

## Verification scope

The five new source modules are ObservationCoefficientRecovery,
ObservationFullCoordinates, ObservationMultiplicationPolynomials,
ObservationSourceMetrics and PolynomialOriginalOrbit. Their ten theorem
declarations are included in the project root and transitive axiom audit.
The authoritative whole-project run is recorded in verification/result.json
and the associated build and axiom logs. Machine checking establishes the
stated theorems under their stated premises; theorem counts, finite tests
and file hashes do not establish the still-open P0 conclusion.
