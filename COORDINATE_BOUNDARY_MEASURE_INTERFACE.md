# Coordinate Haar measure and original boundary strips — F46

Historical scope: F47 proves a conditional quotient-metric tube bound
from the literal coset-distance formula and locally Lipschitz coordinates.
Their derivation from the intended Malcev/Lie data remains open. See
QUOTIENT_BOUNDARY_GEOMETRY_INTERFACE.md for the current interface.

P0 and WeightedCapture remain unproved. F46 proves coordinate-volume
invariance and its exact relation to the original quotient probability,
then proves linear strip bounds for the specified original section.
It does not yet prove the original quotient-metric tube estimate.

## Literal hypotheses

The actual base group G has a coordinate homeomorphism
`coord : G ≃ₜ (Fin m → ℝ)`. Its actual left multiplication satisfies

```
coord(g*u)_i = coord(u)_i + q(g,i)(coord(u)),
```

where q(g,i) is a real coordinate polynomial supported only on variables
j < i. The original subgroup Gamma has exactly the full integer-grid
coordinate image. It is the original discrete subgroup; the quotient may
be nonnormal. The chosen domain is the same translated half-open unit
cell D_a as in F44. All dimensions, including zero, are covered.

These are explicit original-coordinate hypotheses. This checkpoint does
not derive them, their rational complexity, or their uniform heights from
the full abstract Malcev/Lie data.

## Volume preservation proved internally

`TriangularVolume.lean` proves the stronger measurable statement: for
every finite dimension, if each q_i is measurable and depends only on
strictly earlier coordinates, the map u_i -> u_i + q_i(u) preserves
Lebesgue volume.

The proof splits the last coordinate from its prefix. Induction treats
the prefix; the last coordinate is an ordinary real translation depending
measurably on that prefix. The product-measure skew-product theorem
combines these facts. No derivative formula, determinant premise, or
unproved coordinate-invariance assumption is used.

Literal polynomial support supplies measurability and prefix dependence.
An exact dimension-one counterexample shows that allowing the correction
to cancel the current coordinate collapses volume to a point and fails
to preserve it. This is not a counterexample to P0.

`CoordinateHaarMeasure.lean` defines the actual coordinate measure as the
pushforward of Lebesgue volume by coord^{-1}. It proves:

- original left translations preserve that measure;
- original compact sets have finite mass and nonempty open sets have
  positive mass;
- the measure is therefore Haar;
- every translated half-open unit coordinate cell has mass exactly one.

## Exact original quotient probability

`CoordinateQuotientMeasure.lean` restricts this actual coordinate Haar
measure to D_a and pushes it through the original map G -> G/Gamma.

F44 supplies the strict domain and quotient compactness. F42 supplies
right invariance of ambient Haar from the actual cocompact lattice.
The resulting coordinate-cell quotient measure has total mass exactly
one and is invariant under the whole original group. F43 uniqueness then
identifies it with every specified original invariant probability mu.

Thus the coordinate integration model is proved to be the original
quotient probability. It is not a substitute probability chosen for a
convenient estimate. No original observation section is changed.

## Explicit boundary-strip estimate

For each coordinate i, the lower strip is the box with that coordinate in
[a_i,a_i+t] and the other coordinates in their unit intervals. The upper
strip uses [a_i+1-t,a_i+1]. Each has volume ofReal(t). The union B_t of
all 2m strips satisfies

```
volume(B_t) <= ofReal(2*m*t).
```

The theorem holds for all real widths using the positive-part convention;
its intended geometric application has t >= 0. It also handles dimension
zero. No finite sampling is used.

For the sup metric on the actual coordinate space, points inside the
closed unit cell within distance t of its actual coordinate faces belong
to B_t. This proves the corresponding coordinate-space tube bound.

Every specified original section c with representatives in D_a fixes all
points of D_a, by unique original right corrections. Its descended section
s_c on the original quotient is measurable by F44. Consequently,
`original_section_boundary_strip_mass` proves, for the actual invariant
probability mu,

```
mu {x : G/Gamma | coord(s_c(x)) belongs to B_t}
  <= ofReal(2*m*t).
```

The same pushforward formula bounds any measurable original quotient
event whose representatives in D_a are covered by those coordinate strips.

## Remaining geometric and P0 interfaces

The following distinctions are essential:

1. The coordinate-space tube is not automatically the tube in the
   original quotient metric. One must quantitatively lift/cover the
   original face-image neighborhood and control the relevant coordinate
   maps and lattice translates. No such covering is assumed proved here.
2. F45's base cutoff has Lipschitz constant 1/t, but its product with the
   original observation still requires the actual smooth-chart bounds
   and periodic fiber-face compatibility, uniformly as O(1/t).
3. The intended compatible quotient metrics and uniform base-projection
   constant must be connected to the full original Malcev/Lie data.
4. A different specified fundamental domain still requires exact matching;
   the specified section is never silently replaced by the F44 cell.
5. Uniform rational heights, matching the external quantitative Leibman
   input and original interval normalization, general descents and their
   termination, original-frequency extraction/realization, and the final
   WeightedCapture/P0 theorem remain open.

The historical twelve incorrect three-dimensional applications remain
unused. No status change is asserted for U0 or P2-CSE.
