# Full original H rational logarithmic coordinates and lattice — F59

Historical checkpoint. F60 identifies the actual rational Lie basis and
bracket in the same original chart and bases; see
ORIGINAL_RATIONAL_LIE_BASIS_INTERFACE.md and STATUS.md for current scope.

Checkpoint date: 2026-09-23. F59 adds nine theorem declarations to F58's
1592. The checked total is 1601 after the full project audit. P0 and
WeightedCapture remain unproved.

## Original source and scope

The manuscript's sections/04-freezing.tex, equation H-exp and the following
lattice paragraph, require the full original observation group H. F58 had
constructed a global time-one equivalence and an explicit inverse, but
only the base G denominator statement had been assembled. An operator
polynomial is not yet a literal rational polynomial array in every full
coordinate. F59 supplies that missing assembly.

The original phase12_capture_contract.json and FORMALIZATION_CONTRACT.md
remain unchanged. This checkpoint concerns the original group itself;
it neither constructs circle-frequency roots nor makes a quotient
logarithm single-valued. All-label capture and original-response transfer
are separate obligations.

## Scope obstructions retained

The checked F56 translation example excludes replacing the integrated
fiber by tQ. F54's lattice obstructions exclude treating the logarithmic
lattice image as an additive subgroup or deducing uniform denominator
heights from rationality alone. F59 uses the actual factorial operator,
its two-sided inverse, and the entire original lattice in the same basis.
None of these obstructions is a counterexample to P0.

In particular, the inverse operator must be evaluated at Log_G(g), rather
than at the raw group coordinates of g. The new inverse array performs
this substitution explicitly, while leaving every original fiber
coefficient unchanged.

## Literal rational arrays

For the existing rational tensor A, write

```
M_ij(v) = sum_s A_ijs v_s,
R_0,i(v,w) = w_i,
R_(n+1),i(v,w) = sum_j M_ij(v) R_n,j(v,w).
```

`iterated_differential_polynomial_eval` proves, for every n, v and original
Q, that R_n,i(v,bR(Q)) is exactly the i-th coefficient of D(v)^n Q.
The argument is induction on n and the actual differential-coordinate
identity. It is not a finite test or an asserted matrix identification.

For an arbitrary fixed rational polynomial E, summing E_n R_n,i gives
`fiberOperatorPolynomial A E i`. Its evaluation is proved equal to the
original endomorphism polynomial E(D(v)) applied to Q, including the
restriction of rational scalars on the real endomorphism algebra.

Let EG and LG be F58's literal base arrays. The forward full array is

```
S(v,w) = (EG(v), coordinates of E(D(v)) Q),  w = bR(Q).
```

The inverse full array is

```
T(x,y) = (LG(x), coordinates of L(D(LG(x))) P),  y = bR(P).
```

Both are defined as multivariate rational polynomials: base variables
are embedded by renaming, and the inverse fiber polynomial is composed
with the literal base logarithm by polynomial substitution. The generic
evaluation lemmas are then applied to the actual constructed original
time-one equivalence, so their representation premises are discharged.

## Exact quantifiers and actual map

`original_integral_basis_rational_log_coordinates` starts from precisely
the original rational joint law, strict triangular law, original base
integer-grid presentation and rational original observation basis.
It constructs c, d, compatible full integer/real bases bZ and bR,
rational original function representatives, K, A, E, L, logCoord and S,T.
All these choices precede every unrestricted tangent v, original
observation Q and original group element a. K is positive and D(v)^K=0
for every v. Both fiber inverse identities remain in the conclusion.

The theorem proves:

* logCoord is an equivalence on the actual original H;
* its inverse at (v,bR(Q)) is the actual original subgroup's time-one value;
* its inverse formula is the original base logarithm and original fiber inverse;
* S and T represent the two coordinate maps globally, in the same bR;
* logCoord(1)=0.

The bZ is a basis of the entire original integer observation lattice,
not of a selected finite-index replacement.

## Both full original lattice inclusions

`original_integral_basis_full_logarithmic_lattice` discharges the rational
map and origin premises of the earlier denominator theorem. It uses the
existing equivalence between the entire H lattice and the full integer
grid in the same bZ,bR coordinates. There exists one natural den>0 such that

```
for every integer vector z, some original lattice gamma has
    logCoord(gamma) = den*z;
for every original lattice gamma, some integer vector z has
    den*logCoord(gamma) = z.
```

The denominator is selected before either universal quantifier. No
additive closure of the logarithmic image is used. The theorem proves
existence for each fixed structural presentation; it gives no uniform
height bound over a varying class of presentations.

## Still open

Identification of these coordinate tangents and constructed maps with the
intended rational Lie basis and standard exponential/logarithm remains to
be supplied for the intended external weak-basis interface. Uniform
heights, adapted Malcev and external metric/test/filtration/interval
matching, general structural descents and quantitative termination, and
original-frequency realization with all labels, circle roots, quadratic
freedom, original weights and full responses remain open. These internal
matching obligations are not reclassified as external deep theorems.

The next identification must also respect conventions. The existing
`originalCoordinateVelocity` differentiates the first multiplication
input and gives a right-invariant field. Mathlib's `GroupLieAlgebra`
uses `mulInvariantVectorField`, defined through the derivative of left
multiplication. Subgroup uniqueness and the new coordinate inverse do
not by themselves identify these bracket conventions. The same bR and
its rational original function representatives can be supplied to
`original_observation_coordinate_lie_group`; a subsequent proof must
connect its actual tangent space, bracket and subgroup derivatives to
the rational basis required downstream.

The four new modules are ObservationFiberPolynomials, ObservationLogCoordinates,
OriginalFullLogarithm and OriginalFullLogLattice. The full audit includes
every new theorem and checks its transitive foundational dependencies.
