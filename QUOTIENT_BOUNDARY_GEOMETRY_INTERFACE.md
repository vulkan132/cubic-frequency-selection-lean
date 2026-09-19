# Original quotient boundary geometry — F47

Historical scope: F48 derives the original cutoff product estimate from
controlled actual pair lifts, and constructs short base paths from
locally Lipschitz forward/inverse coordinates. Intended metrics and pair
lifts still require construction. See ORIGINAL_CUTOFF_GEOMETRY_INTERFACE.md.

P0 and WeightedCapture remain unproved. This checkpoint adds 17 theorem
declarations, proving a conditional quotient-metric tube bound for the
actual original cell and invariant probability. It constructs uniform
local constants from local Lipschitz coordinates; it does not construct
the intended Malcev metric or prove those coordinates locally Lipschitz.

## Exact inputs and quantifiers

Fix a metric topological group G, a coordinate homeomorphism
`coord : G ≃ₜ (Fin m → ℝ)`, the literal strictly triangular polynomial
left-multiplication laws, and the original discrete subgroup Gamma whose
coordinate image is exactly the full integer grid. Fix the translated
half-open unit cell D and set S to the image of its frontier under the
original quotient map. The measurable structures have the stated Borel
compatibilities. A metric on the actual quotient must satisfy the literal
formula

```
dist_Q(g Gamma, h Gamma) = inf_gamma dist_G(g, h*gamma).
```

This equality is an explicit hypothesis, not an assertion for arbitrary
group metrics. No nearest representative or normality of Gamma is assumed.

If `coord` is locally Lipschitz for the supplied group metric and ordinary
finite coordinate metric, there exists C >= 0, chosen before every
specified full-group invariant probability mu and every t > 0, such that

```
mu({x | S.Nonempty and infDist(x,S) < t}).toReal <= C*t.
```

All group, coordinate, lattice, domain and metric data precede C. There is
no dependence on any orbit, N, or observation coefficient in this result.
No height bound, computable value, or uniform bound over varying rational
presentations is asserted.

## Proof content

1. The original cell's closure, interior and frontier are exactly the
   closed coordinate box, open coordinate box, and coordinate faces.
   Uniqueness of original right corrections implies that every original
   lattice translate of the frontier avoids the cell's interior.
2. The distance formula makes the original quotient map 1-Lipschitz and
   S compact. A strict quotient-distance bound lifts to an actual original
   lattice translate of a frontier point by the infimum property.
3. If the group points are less than r apart and coordinates satisfy a
   comparison with constant L, a cell representative in the quotient
   t-tube lies in the original coordinate strips of width L*t for t<=r.
   No enumeration or truncation of the original lattice is used.
4. F46's actual quotient measure identification and strip volume estimate
   give tube mass at most 2*m*L*t for 0<t<=r. Probability mass at most one
   extends this to `(2*m*L + 1/r)*t` for every t>0.
5. A compact thickening of the original cell closure and local Lipschitz
   continuity supply one L and r, including pairs whose second point lies
   outside the cell. Thus those constants are constructed internally.

An exact obstruction proves that no L>=0 can satisfy
`abs(x) <= L*abs(x^3)` on [0,1]. Mere topological coordinate compatibility
cannot replace quantitative regularity. This is not a counterexample to P0.

## Remaining interfaces

- Derive the intended group and quotient metrics, the literal distance
  formula and local Lipschitz coordinate property from the original
  rational Malcev/Lie data. Match the specified original fundamental
  domain exactly if it differs from the proved translated unit cell.
- Prove the uniform Lipschitz constant of the actual H-to-G projection and
  the O(1/t) Lipschitz bound for the original cutoff observation, including
  chart and periodic fiber-face compatibility. The quotient map's
  1-Lipschitz property here is not the H-to-G projection estimate.
- Connect the external quantitative Leibman input and original interval
  normalization; prove necessary uniform heights, general descents and
  termination; extract and realize original-frequency models and assemble
  WeightedCapture and P0 with all original labels, responses and weights.

No external deep premise or project axiom is introduced. The historical
twelve invalid three-dimensional applications remain unused; no resolution
of P2-CSE or U0 is claimed.

Sources: `GMZP0/CoordinateCellFrontier.lean`,
`GMZP0/QuotientBoundaryTube.lean`, `GMZP0/OriginalMetricBoundary.lean`,
`GMZP0/CompactCoordinateLipschitz.lean`. Every new theorem is included in
the kernel axiom audit. Compilation validates these exact conditional
statements and does not discharge their geometric hypotheses.
