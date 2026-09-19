# Original observation cutoff geometry — F48

Historical scope: F49 constructs controlled original pair lifts and the
global projection constant from compatible metrics, their literal coset
formulas and locally Lipschitz actual coordinates. It assembles original
orbit forcing and the exact N-normalized mean transfer. Those metric and
coordinate inputs still require construction. See COMPACT_METRIC_LIFT_INTERFACE.md.

P0 and WeightedCapture remain unproved. F48 adds 17 theorem declarations.
It derives the original cutoff observation's O(1/t) Lipschitz bound from
explicit compact pair-lift geometry, without assuming that final product
bound. It also constructs the required short base paths from local metric
regularity of both directions of the actual coordinate homeomorphism.
The intended metrics, controlled quotient lifts and projection constants
still need construction from the original Malcev/Lie data.

## Original objects and quantifiers

Use the original group G, discrete subgroup Gamma, function module V,
observation group H and its actual lattice Gamma_H. Keep the specified
section c, its original right correction gamma_g, and the exact observation

```
Psi((g,P) Gamma_H) = e(P(gamma_g)).
```

The section has range in a fixed strict domain D with compact closure;
every original g has exactly one right correction into D. Set S to the
actual image of frontier D under the original quotient map. No unrelated
coordinatewise fractional-part map or alternative section is substituted.

Fix a compact base chart set K and an actual finite real basis b of V.
The supplied pair-lift data have constants M>=0, B>=0, r0>0, chosen before
all original quotient points x,y. Whenever dist(x,y)<r0 they give actual
representatives u,v in H with

```
u Gamma_H = x,  v Gamma_H = y,
u.base, v.base in K,
dist(b.equivFun u.obs, b.equivFun v.obs) <= M*dist(x,y),
dist_G(u.base,v.base) <= B*dist(x,y).
```

These representatives need not be the canonical representatives; their
quotient observation equals the unchanged original observation by its
already proved exact lattice invariance. This permits genuine periodic
fiber identifications rather than falsely identifying opposite real
fiber faces. The compact pair-lift existence and these bounds are still
supplied metric geometry, not proved here from the paper's hypotheses.

The actual base coordinate homeomorphism and its inverse are assumed
locally Lipschitz, and the original base quotient metric satisfies its
literal coset-infimum formula. These yield one smaller radius and a
uniform projected base-path bound, both before every point pair.

Finally supply a uniform Lipschitz constant J for the actual H-to-G
quotient projection. Then one C>=0 is chosen before every 0<t<=1, and

```
LipschitzWith (toNNReal(C/t)) ((chi_t o pi)*Psi).
```

The fixed structural objects, basis, section, domain and metric geometry
precede C. There is no restriction on the sizes of the original observation
coefficients, and no dependence on an orbit or its length. No effective
height bound or uniform estimate over varying presentations is asserted.

## Internal proof

1. All corrections for g in K lie in the original discrete subgroup's
   intersection with K^{-1}*closure(D). This is finite, even though the
   section is not globally continuous.
2. An original representative off S is interior to D. F44's actual
   correction is locally constant there; on a connected continuous path
   avoiding S it is constant. A change of correction therefore forces an
   actual quotient face crossing, with a distance bound whenever the
   projected path has controlled radius.
3. The actual basis identity gives
   `abs(P(gamma)-Q(gamma)) <= sum_i abs(b_i(gamma))*dist(coeff(P),coeff(Q))`.
   The character chord bound and the finite original correction set give
   one constant for every same-correction pair and all real coefficients.
4. For nearby original quotient points either their observations differ
   by at most L*distance, or the first base point is within A*distance of S.
   This is proved from the actual pair lifts, not assumed for Psi.
5. Product comparison keeps the cutoff multiplying the possible jump:
   `norm(a*u-b*v) <= a*norm(u-v)+abs(a-b)` for a>=0 and norm(v)=1.
   Since chi_t<=dist_to_S/t, the two alternatives give a uniform bound;
   far pairs use norm(Psi)=1. One valid constant is
   `C=L+2*A+J+2/r`, before the cutoff scale t.
6. The locally Lipschitz forward and inverse coordinates supply uniform
   constants on compact thickenings. Actual straight coordinate segments,
   transported by the inverse coordinate map, give uniformly short base
   paths. The original base quotient map is 1-Lipschitz under its literal
   distance formula, constructing the path component of the pair charts.
7. With the explicit actual tube-mass bound, measure-preserving projection
   and invariant probabilities, this product estimate feeds F45's orbit
   theorem. The original zero mean is derived from its constant-translation
   symmetry. One t and alpha precede every finite index type, orbit length
   and original orbit. The external quantitative Leibman conclusion is
   not yet attached.

The exact counterexample in `CutoffJumpObstruction.lean` shows that the
empty-boundary cutoff, identically one, does not make the unit step taking
values 1 and -1 Lipschitz. Thus cutoff regularity alone cannot justify the
paper's product estimate. This is not a counterexample to P0.

## Remaining interfaces

- Construct the intended compatible metrics and their coset-distance
  formulas for both original quotients. Derive the local regularity of
  coordinates and inverse coordinates from full original Malcev/Lie data.
- Construct the controlled original quotient pair lifts above, using the
  actual compact H covering cell and metric control of its base/fiber
  coordinates; prove the original H-to-G projection's uniform constant.
- Match the specified fundamental domain exactly and connect F47's tube
  mass bound to the same geometric presentation and measure throughout.
- Match the external quantitative Leibman theorem and original interval
  normalization; prove necessary uniform heights, general descents and
  termination; extract/realize original-frequency models and assemble
  WeightedCapture and P0 with complete labels and original responses.

These internal geometry obligations have not been reclassified as external
deep theorems. The twelve invalid historical three-dimensional applications
remain unused. No change to the open status of P2-CSE or U0 is asserted.

## Sources and verification scope

The paper source is `sections/04-freezing.tex`, especially the original
observation and cutoff discussion leading to equation `boundary-bound`.
New Lean sources are `ObservationCorrectionGeometry`,
`ObservationBranchEstimate`, `BoundaryCutoffGluing`,
`OriginalObservationCutoffGeometry`, `CompactCoordinatePaths` and
`CutoffJumpObstruction` under `GMZP0/`. All declarations are registered in
the kernel axiom audit. Its success validates these exact statements, not
their remaining metric hypotheses or the unproved P0 target.
