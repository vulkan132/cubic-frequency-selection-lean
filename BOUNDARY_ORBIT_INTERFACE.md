# Boundary cutoffs and original orbit control — F45

Historical scope: F46 proves coordinate Haar invariance, exact original
quotient-probability identification and explicit coordinate-strip mass
bounds. See COORDINATE_BOUNDARY_MEASURE_INTERFACE.md for the current
frontier. Original quotient-metric tube coverings and the original
observation cutoff's Lipschitz bound remain open.

P0 and WeightedCapture remain unproved. This checkpoint proves the
boundary-error calculus for the unchanged original observation under
explicit quantitative geometric hypotheses. It does not prove those
geometric hypotheses from the full Malcev/Lie presentation.

## Source and original objects

The source is `GMZ_P0_Arxiv_Paper/sections/04-freezing.tex`, subsection
“A fixed observation with mean zero”, especially equation `boundary-bound`.
The original observation is still `quotientObservation V c` on the actual
`ObservationGroup V / observationLatticeSubgroup V Gamma`. Its base map is
still `observationQuotientBaseProjection V Gamma`, and `c` is the specified
original section. No orbit point, coefficient, frequency or original
response is replaced.

## Explicit construction

For the actual base boundary set S and t > 0, let d(x,S) be the metric
distance. For nonempty S define

```
b_t(x) = min(1, max(0, 2 - d(x,S)/t)),
chi_t(x) = 1 - b_t(x).
```

For empty S, define b_t = 0 and chi_t = 1. This case matters because
Mathlib's real-valued `infDist` is zero on the empty set. `boundaryTube`
therefore includes the explicit nonempty-set condition.

`MetricBoundaryCutoff.lean` proves:

- both functions lie in [0,1]; chi_t vanishes where d <= t and equals one
  outside the open 2t-tube;
- both functions have Lipschitz constant at most 1/t;
- b_t is measurable and integrable for any finite Borel base measure nu;
- the integral of b_t is at most the actual measure of the 2t-tube.

These claims do not require smoothness, a nonempty boundary, or a
pre-existing O(t) estimate. They do not establish O(t) by themselves.

## Actual orbit estimate

`LipschitzOrbitDiscrepancy` tests every bounded complex Lipschitz function F:
with sup-bound B and Lipschitz constant L, the difference between the
complete finite orbit average and its integral is at most alpha(B+L).
This explicitly records the sum convention for the Lipschitz norm.

Let pi preserve the actual measures mu and nu, with Lipschitz constant J.
Let the original unit-norm observation psi have cutoff
F_t = (chi_t o pi) psi, of Lipschitz constant K and integral zero. Then
`boundary_orbit_observation_bound` proves

```
|mean_i psi(u_i)|
  <= nu(boundaryTube S (2t)) + alpha(2 + K + J/t).
```

The error is pointwise exactly b_t(pi(x)), so this estimate retains every
original boundary visit. The pulled-back majorant's integral is identified
through the actual measure-preserving projection. F43 proves that
projection property for the original invariant probabilities under its
explicit lattice hypotheses.

`orbit_boundary_visit_fraction_le` also bounds the fraction of actual
visits to the t-tube by

```
nu(boundaryTube S (2t)) + alpha(1 + J/t).
```

`OriginalBoundaryOrbit.lean` specializes the results to the original
quotient observation. Its zero mean and integrability are derived from
the actual invariant probability, constants in V, the measurable specified
section, and the previously proved constant-translation symmetry.
Zero mean is not a new premise in these original-observation theorems.

## Exact uniform quantifiers

Suppose fixed nonnegative C,A and fixed projection constant J satisfy,
for every 0 < t <= 1:

1. nu(boundaryTube S (2t)) <= C t;
2. the original cutoff has Lipschitz constant at most A/t.

For every gamma > 0 the proved theorem chooses t and alpha > 0 **before
every finite index type, every orbit length and every orbit**. Every
original orbit with observation mean larger than gamma fails the above
alpha-discrepancy condition. All original real coefficients may vary
through the orbit.

The proof uses D = A+J and the explicit choices

```
t = min(1, gamma / (4(C+1))),
alpha = gamma / (4(2+D/t)).
```

They give Ct + alpha(2+D/t) <= gamma/2. The scale is chosen first and
the discrepancy tolerance second. Neither depends on the finite orbit.

## Exact obstruction

`null_boundary_full_orbit_visits` uses normalized Lebesgue measure on
[0,1]. The boundary {0} has measure zero, yet every finite nonempty
constant-zero orbit has mean b_t equal to one for every t > 0.
This is a general exact proof, not a finite computational test, and it
does not claim a counterexample to P0.

## Remaining interface

- Identify the original specified fundamental domain and its actual face
  image S. F44 covers sections taking values in its proved translated
  half-open unit coordinate cell; it does not identify a different domain.
- From the full rational Malcev/Lie data, provide the intended compatible
  metrics, a uniform projection bound J, and the genuine O(t) tube bound.
- Prove the original cutoff's uniform O(1/t) Lipschitz bound, including
  chart changes and periodic fiber-face matching. F44 local continuity
  does not imply this quantitative assertion.
- Match the external quantitative Leibman statement to these actual
  orbit tests and the original interval normalization and filtration.
  No external theorem is introduced as a project axiom.
- Complete uniform rational heights, general structural descents and
  termination, original-frequency extraction/realization, and the final
  WeightedCapture/P0 proof.

Theorems here leave these assumptions visible rather than repackaging
them as a supplied boundary-error theorem.
