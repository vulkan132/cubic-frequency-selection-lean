# Constructing compatible right-invariant source metrics — F51

Historical checkpoint. F52 instantiates the actual observation-group law
and base/fiber maps and assembles original orbit forcing; the current
scope and remaining interfaces are in ORIGINAL_POLYNOMIAL_ORBIT_INTERFACE.md.

P0 and WeightedCapture remain unproved. F51 adds 27 theorem declarations.
It constructs the source and actual coset metrics from a finite-dimensional
coordinate homeomorphism, literal joint polynomial group multiplication,
and the original discrete lattice compact cover. No source right isometry
or local coordinate regularity is assumed in that final construction.

## A concrete source metric

Start with the original topological group G and an initial proper metric
d0 compatible with its topology, with locally Lipschitz multiplication.
Define one fixed peak and its entire original translate family:

```
phi(x) = max(0, 1 - d0(x,1)),
F_g(z) = phi(g*z),
dR(g,h) = uniform distance between F_g and F_h.
```

The functions F_g are actual bounded continuous functions on the original
group. The peak has its unique value one at the original identity, so
evaluation at g inverse proves g -> F_g injective. Pullback of the uniform
metric therefore constructs a genuine metric on the same original group.
Right multiplication by a merely permutes the full auxiliary variable
z -> a*z. Hence every original right translation is isometric, preserving
noncommutative multiplication order throughout.

Both directions of local metric comparison are proved:

- For a fixed original compact set K, a nonzero peak at g*z implies
  z belongs to the compact set K inverse times the closed original unit
  ball. Local Lipschitz multiplication on the relevant compact product
  gives a uniform bound dR(g,h) <= C_K*d0(g,h) for g,h in K.
- Evaluation at h inverse gives
  min(1,d0(g*h inverse,1)) <= dR(g,h). If dR(g,h)<1, multiplication on the
  compact product of the original closed unit ball and K bounds d0(g,h)
  by a constant times dR(g,h). Larger distances on K use its finite diameter.
- The new unit ball about each h lies in the compact set of original unit
  ball elements multiplied on the right by h. Thus the inverse identity
  is locally Lipschitz on an entire new-metric neighborhood, without first
  assuming topology agreement. The two identities prove exact topology
  agreement; the final metric preserves the original topology definitionally.

Constants for a fixed K precede all its point pairs. Initial properness is
used to prove compactness of original coordinate balls; properness of the
new bounded metric is neither asserted nor used.

## Deriving the initial data from literal coordinates

Let coord be the actual homeomorphism G -> R^m. Pulling back the finite
coordinate norm constructs the initial metric with the original topology;
the actual coordinate map is isometric and its balls are compact.

Supply the literal joint coordinate formula

```
coord(g*h)_i = p_i(coord(g), coord(h))
```

for fixed ordinary multivariate polynomials p_i. Polynomial induction
proves C1 regularity of evaluation, and finite coordinate products give
local Lipschitz multiplication. The constructed right metric therefore
has locally Lipschitz actual coordinates and inverse coordinates.
`polynomial_group_right_metric` derives all these properties from this
same original presentation, without requiring nilpotence or a separate
abstract differentiable group structure.

`polynomial_group_and_coset_metrics` additionally takes the original
discrete subgroup Gamma and compact K meeting every actual right coset.
It constructs both source and quotient metrics, their original topologies,
every right isometry, both local coordinate regularity statements, and the
literal original coset-infimum formula of F50. Gamma need not be normal.
The existing original triangular-cell reduction supplies such a compact
cover when its exact integer-grid hypotheses apply.

The joint polynomial formula is an exact presentation of the actual group
law. It is stronger than a polynomial-in-the-second-variable formula with
unrestricted dependence on the first variable. The construction does not
silently promote the latter into a joint polynomial formula.

## Scope obstruction and remaining interfaces

The new distance is at most one everywhere. Even on the additive real
group, no nonnegative finite L can bound every original coordinate |x|
by L*dR(x,0): choose x=L+1. This checked obstruction rules out claiming
global coordinate bi-Lipschitz equivalence. The proved local and fixed-
compact-set bounds are the scope used for geometric cutoff estimates.
This is not a counterexample to P0.

The next original-data connection is to instantiate this construction for
the actual observation group H=G times V: identify its joint polynomial
coordinate multiplication from the original semidirect law and polynomial
translation presentation, and prove local regularity of the actual base
projection and actual basis-coefficient map in the same chosen metrics.
Then instantiate the F50 original cutoff theorem and the F49 complete-orbit
theorem with those metrics. These assembled instantiations are not claimed
by the present generic metric construction.

Still open are the necessary quantitative comparison with the metric and
tests of the permitted external Leibman theorem, uniform rational heights
and complexity, its exact filtration and original interval smoothness norm,
general descents and termination, original-frequency extraction/realization,
and final WeightedCapture/P0 with all labels, original responses/weights,
vertical freedom and circle root branches retained. Compactness here does
not give a uniform effective bound over varying presentations.

The historical twelve invalid three-dimensional applications remain unused.
P2-CSE and U0 remain open. No new external deep theorem or project axiom is
introduced. Compilation certifies these precise statements and hypotheses,
not completion of P0.

Sources: `RightRegularMetric`, `RightRegularMetricBounds`,
`CompatibleRightMetric`, `PolynomialCoordinateMetric`,
`PolynomialGroupRightMetric`, `PolynomialCosetMetric`, and
`RightMetricGlobalObstruction` in `GMZP0/`.
