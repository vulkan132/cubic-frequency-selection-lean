# Actual compact metric lifts and original orbit forcing — F49

Historical scope: F50 constructs the quotient metrics and formulas from
closed original lattices and source right lattice isometries. Source
metric construction and local coordinate regularity remain open. See
ORIGINAL_COSET_METRIC_INTERFACE.md for the current frontier.

P0 and WeightedCapture remain unproved. F49 adds 16 theorem declarations.
It constructs the compact pair
lifts and global H-to-G projection constant previously supplied at F48.
It assembles original tube measure, cutoff geometry, section measurability,
measure projection, zero mean and orbit testing in one conditional theorem.
The original N-normalized sum is transferred to the full interval mean
with the exact cardinality condition. Intended metric construction and
coordinate regularity remain internal, unproved geometric interfaces.

## Literal metric inputs

Keep the original group G, observation group H=G times V, original
lattices Gamma and Gamma_H, original basis coordinates, and specified
section c. Supply actual metrics on G and the two quotients, and a
pseudometric on H whose topology is explicitly equal to H's original
product topology. Require the actual coset-distance formulas on both
quotients:

```
dist_Q(g Gamma,h Gamma) = inf_gamma dist_G(g,h*gamma),
dist_QH(u Gamma_H,v Gamma_H) = inf_lambda dist_H(u,v*lambda).
```

These formulas are not valid for arbitrary supplied metrics and are not
constructed in this checkpoint. Require local Lipschitz regularity of
the original G coordinate homeomorphism and its inverse, the actual map
H -> G taking the base coordinate, and the map H -> R^d taking the actual
V-basis coefficients. No uniform constants for these maps are supplied.

The actual compatible integer and real fiber bases are used with their
pointwise identification; earlier rational-presentation results construct
such bases. The assembled orbit theorem also takes the literal triangular
group laws, strict earlier-coordinate polynomial support, full original
integer grid, continuous original observation functions, and constants
in V. The specified section has range in the same translated half-open
coordinate cell used by the original tube estimate.

All metric and coordinate data are fixed before the constants, N, orbit
length, orbit points and unrestricted observation coefficients. F49 does
not derive these metric inputs from the full Malcev/Lie presentation and
does not assert uniform height bounds across varying presentations.

## Constructed geometry

1. A compact original covering set C and the literal coset metric give
   compactness of the metric quotient. Restriction of the quotient map
   to C is a continuous surjection from a compact space to a Hausdorff
   space; hence the metric has exactly the original quotient topology.
2. A compact thickening E of C and r>0 are selected before all pairs x,y.
   The first representative stays in C; an actual lattice translate
   supplies the second in E, with distance at most twice dist(x,y).
   The diagonal uses the same representative. For distinct quotient
   points the infimum gives a strict bound, not a nearest lattice point.
3. Each actual locally Lipschitz coordinate map has a finite Lipschitz
   bound on E. This proves uniform base and fiber-coordinate difference
   bounds on the original lifts, before all nearby point pairs.
4. H's compatible topology transports the already proved original compact
   base/fiber cell and local compactness. Reduction uses the actual base
   lattice correction and its pullback before the original integer fiber
   rounding. Projecting E gives the compact base chart set for F48.
5. The original H-to-G quotient projection has a uniform local bound from
   those lifts. The actual base metric quotient is compact, so its bounded
   image extends that bound to all point pairs. One valid general constant
   is `B + diam(range(pi))/r`. The global projection constant is a conclusion.
6. F48's coordinate segments construct short base paths. Its finite actual
   corrections, boundary-crossing argument and exact character evaluation
   then yield the unchanged original cutoff observation's C/t Lipschitz
   bound, with C before all 0<t<=1. No pair-lift, path, global projection
   or product-Lipschitz premise remains in `original_observation_metric_cutoff`.

## Original orbit and normalization

`original_metric_boundary_nonequidistribution` additionally derives the
strict original cell, its compact closure and specified-section
measurability. F47 supplies the actual quotient tube mass from these same
coordinates. F43 identifies the actual probability projection, and the
original constant-translation symmetry gives zero cutoff mean.

For every gamma>0, it selects t>0, t<=1 and alpha>0 before every finite
index type and every original orbit. A large full uniform original
observation mean forces failure of alpha-discrepancy. The same t and alpha
also work before every N>0 and every complete finite index set I with
card(I)<=N whenever

```
gamma < norm((sum_i Psi(u_i))/N).
```

The theorem proves both `gamma*N < card(I)` and failure of discrepancy,
retaining every original orbit point. It does not delete endpoints, change
the observation, or replace the original divisor N by card(I) silently.
The two-point constant-one example with N=1 has N-normalized mean 2 and
uniform mean 1; it disproves the transfer if the cardinality bound is
omitted. It is not a counterexample to P0.

## Still open

- Construct the intended actual group and quotient metrics with the literal
  distance formulas and the stated local coordinate regularity from full
  original rational Malcev/Lie data. These remain internal geometry work,
  not newly designated external deep theorems.
- Match any differently specified original fundamental domain exactly.
  Derive necessary uniform rational complexity, heights and character bounds.
- Connect the permitted external quantitative Leibman theorem to the exact
  filtration, metric tests, original interval and interval smoothness norm.
  The N-versus-cardinality mean conversion is now proved; this does not
  prove that entire external-theorem interface.
- Complete general structural descents and uniform termination, original
  frequency model extraction/realization, and final WeightedCapture/P0 with
  full labels, original responses, weights and all circle root branches.

The historical twelve invalid three-dimensional applications remain unused.
P2-CSE and U0 remain open. No project axiom or new external deep premise is
introduced. Full compilation and axiom auditing certify only the exact
formal statements above, not their remaining geometric hypotheses or P0.

Sources: `CompactCosetLifts`, `UniformLocalProjection`,
`ObservationMetricLifts`, `ObservationProjectionLipschitz`,
`OriginalMetricCutoff`, `OriginalMetricBoundaryOrbit` and
`OrbitIntervalNormalization` in `GMZP0/`; the paper's fixed observation and
boundary estimate discussion in `sections/04-freezing.tex`.
