# Constructing the actual coset metrics — F50

Historical scope: F51 constructs the required source metrics, right
isometries and local coordinate regularity from literal joint polynomial
group coordinates. Actual H presentation and base/fiber-map instantiation,
and quantitative matching to the external metric remain open. See
POLYNOMIAL_RIGHT_METRIC_INTERFACE.md for the current frontier.

P0 and WeightedCapture remain unproved. F50 adds 19 checked theorem
declarations. The quotient metrics and their infimum formulas are now
constructed from explicit source-metric inputs; constructing those source
metrics and their coordinate regularity from full original Malcev/Lie data
remains an internal obligation.

## Exact inputs and construction

Let G be the original group with a pseudometric making it a topological
group, and Gamma its original closed subgroup. Require every actual map
`x -> x*gamma`, for gamma in Gamma, to be an isometry. No normality of Gamma
is assumed. Use the entire original coset in

```
d(g Gamma,h Gamma) = infDist(g, {h*gamma : gamma in Gamma}).
```

Actual lattice permutations prove independence of both representatives.
Inverse right translations prove symmetry; infimum inequalities prove the
triangle inequality. Each original coset is closed, so distance zero forces
equality of the original cosets. These results construct a genuine metric
on the actual quotient type. No nearest representative is assumed or chosen.

An actual compact set C meeting every original coset makes the quotient
map from C continuous and surjective. The metric topology is therefore
exactly the original quotient topology. The final metric retains that
topology definitionally, the literal infimum formula, and a 1-Lipschitz
original quotient map. Neither a new quotient nor a normal closure is used.

## Connection to the original observation

The original integer-valued subgroup of V is the intersection, over every
original gamma, of the inverse images of Z under evaluation at gamma.
Continuous evaluation and closedness of Z prove this subgroup closed in
the original pointwise topology. This argument needs neither discreteness
nor a finite replacement for the original evaluation conditions. Together
with closedness of Gamma, it proves the actual Gamma_H closed in H's
original product topology.

`original_observation_cutoff_from_isometric_actions` takes source metrics
on G and H, with H's topology explicitly equal to the original product
topology. It assumes isometry of every actual right Gamma and Gamma_H
translation, locally Lipschitz actual base/fiber coordinates and both
directions of the original base coordinate homeomorphism. The original
finite compatible integer/real bases, compact base cover, and continuous
observation functions supply H's actual compact cell and topological group.

The theorem constructs both quotient metrics, proves their exact original
topologies and infimum formulas, and applies F49 to derive one global
projection constant J and one L>=0 such that the unchanged original cutoff
observation is L/t-Lipschitz for every 0<t<=1. It takes no independent
quotient metric or quotient-distance formula as a hypothesis. Original
section and actual lattice corrections are retained. The new wrapper ends
at this geometric conclusion; it does not add a quantitative Leibman or
P0 conclusion. F49's conditional full-orbit theorem remains available.

## Obstruction and remaining work

The pullback distance `|x^3-y^3|` is a genuine metric on R. Integer
translation by 1 changes the distance of 0 and 1 from 1 to 7. This exact
checked obstruction prevents dropping the source right-isometry condition
merely because a coordinate pullback is a metric. It is not a P0 counterexample.

Still required:

- Construct suitable original G/H source metrics with the required right
  isometries and local coordinate regularity from the full rational
  Malcev/Lie data. Match their quantitative tests to the metric in the
  permitted external theorem. This is internal work, not a new deep input.
- Match any different specified domain exactly and derive the necessary
  uniform rational complexity, heights and character bounds. The compactness
  arguments here do not supply uniform effective bounds across presentations.
- Connect quantitative Leibman to the exact filtration, original interval
  and smoothness norm; finish general descents and uniform termination.
- Realize the original frequency models and close WeightedCapture and P0
  with all labels, original responses/weights, vertical freedom and circle
  root branches preserved.

The historical twelve invalid three-dimensional applications remain unused.
P2-CSE and U0 remain open. No project axiom is introduced. The Lean checks
certify the stated conditional results; they do not prove the remaining
source-metric hypotheses or P0.

Sources: `CosetDistanceAlgebra`, `OriginalCosetMetric`,
`ObservationLatticeClosed`, `ConstructedQuotientCutoff`, and
`CosetMetricObstruction` in `GMZP0/`.
