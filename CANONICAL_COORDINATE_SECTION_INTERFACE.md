# F44: actual triangular half-open cells and specified original sections

Historical scope: F45 constructs metric boundary cutoffs and proves their
conditional original-orbit estimates with exact uniform quantifiers. See
BOUNDARY_ORBIT_INTERFACE.md for the current frontier. The geometric O(t)
tube and O(1/t) original-observation cutoff bounds are still open.

P0 and WeightedCapture remain unproved. This checkpoint adds 20 theorem
declarations in four modules. Its domain is a fixed translated half-open
unit cell in the actual coordinates. The exact matching condition for an
original section is stated explicitly; no different representative is
substituted into an original observation or response.

## Exact integer reduction in all finite dimensions

For every m, every fixed shift a in R^m and every triangular correction
q_i(u) depending only on coordinates j<i, there is exactly one integer
vector z such that

    z_i + q_i(z) belongs to [a_i,a_i+1) for every i.

Existence is by induction on the number of corrected coordinates. At step
i, choose minus the floor of q_i(z)-a_i and update only z_i. Strict prefix
dependence preserves all earlier corrected coordinates and the current
correction value. Uniqueness is a separate prefix induction using the
fact that two integer translates of the same real number cannot both
belong to one half-open interval of length one. Endpoints are retained
exactly, and m=0 is included.

`polynomial_eval_eq_of_prefix` derives the needed dependence from the
actual support of each lower-coordinate polynomial. The checked diagonal
cancellation obstruction in dimension one shows that allowing current
coordinate dependence destroys uniqueness: q(u)=-u makes every integer
admissible. The lower-coordinate hypothesis is not optional.

## The actual original group and lattice

Assume actual injective coordinates satisfy the literal group law

    coord(g*u)_i = coord(u)_i + aeval(coord(u),q(g,i)),

with every monomial of q(g,i) using only j<i. Assume the original subgroup
Gamma has coordinate image exactly Z^m, with both integrality and full-grid
coverage supplied. The integer reduction above then constructs exactly
one gamma in the original Gamma with g*gamma in the specified coordinate
cell, for every g. It does not introduce an enlarged lattice or drop the
group-law correction.

For a genuine coordinate homeomorphism, the cell is Borel and has compact
closure: the latter is contained in the inverse image of the closed unit
box. Its exact right-correction property proves compactness of the actual
G/Gamma. This compactness is a conclusion in F44, not a new premise.

Under the original discrete-subgroup hypothesis, a measurable section
into this exact strict cell is constructed. Any specified original section
whose range lies in the same cell has the same representative at every
point, by uniqueness of its actual right correction. Thus that specified
section is measurable. This is pointwise identification, not replacement
by an unrelated Borel section.

## Original observation and local continuity

`canonical_original_observation_mean_zero` joins this result to the
literal finite rational polynomial observation presentation. Base Polish
and local compactness follow from the given coordinate homeomorphism;
compactness of G/Gamma and measurability of every specified section in the
proved cell follow internally. With constants in V, one full-H invariant
probability on actual H/Gamma_H is chosen before every such original
section and every bounded measurable base cutoff. The original cutoff
observation is integrable and has zero integral under this same measure.

For any strict right-correction domain S, if the specified original
representative of g lies in the interior of S, continuity of right
multiplication and uniqueness imply that the original correction gamma_g
is constant near g. The specified original section is therefore continuous
there. For coordinate cells, strict inequalities a_i<coord(c(g))_i<a_i+1
verify the interior condition.

The same local constancy makes the original real observation phase and
the pullback of the original quotient observation continuous at every
corresponding observation-group point. Fixed-point evaluation is continuous
in the original pointwise function-space topology. No global continuous
section or uniform Lipschitz bound is inferred.

## Scope that remains open

The original-section conclusion requires its range to lie in the exact
translated half-open coordinate cell proved here. A different specified
fundamental domain needs its own construction or an exact compatibility
argument; F44 does not change the domain of an existing profile.

Full Malcev/Lie data still need to be connected to the literal coordinate
homeomorphism and triangular laws, with the required rational complexity
and uniform height bounds. Homeomorphisms and local continuity alone do
not supply quantitative smooth or Lipschitz estimates. O(t) boundary
neighborhoods, O(1/t) cutoffs/majorants and the resulting actual orbit-visit
bounds remain open, as does invariance of any coordinate-defined measure
whose required properties have not yet been proved.

General structural descents, uniform termination, original-frequency
extraction/realization and final WeightedCapture/P0 assembly remain open.
No new external deep premise or project axiom is introduced. Complete
verification and transitive axiom results are recorded in
`verification/result.json` by `python verify.py`.
