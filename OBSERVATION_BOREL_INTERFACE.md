# F41: measurable original observations and compactly contained Borel domains

Historical checkpoint. F42 constructs full-quotient invariant probability
under the same structural presentation hypotheses and proves global zero
means for every specified measurable section and bounded measurable base
cutoff when V contains constants. See OBSERVATION_GLOBAL_MEAN_INTERFACE.md
for the current scope and remaining quantitative/canonical-data obligations.

P0 and WeightedCapture remain unproved. F41 adds 23 theorem declarations
in five modules. It addresses the measurable-section and measurable-action
inputs of F40, while preserving the original section in every theorem
about the original observation. No external deep premise or project axiom
is added. Quantitative boundary regularity remains open.

## Measurable sections are constructed, not postulated

A surjective local homeomorphism onto a compact Borel space has a
measurable right inverse. The proof chooses finitely many local inverse
charts covering the target, extends each inverse by a fixed value outside
its open domain, and selects the first successful chart in a countable
enumeration of that finite family. It proves measurability and the exact
right-inverse equation everywhere, rather than only almost everywhere.

For the original subgroup Gamma of a topological group G, discreteness
makes G -> G/Gamma a local homeomorphism. Compactness of G/Gamma therefore
supplies an actual measurable `ObservationSection`. For a Polish base,
discreteness proves Gamma closed, the quotient is Hausdorff, and the
quotient measurable structure is its Borel structure; this equality is
proved without assuming Gamma normal.

Every algebraic original section is idempotent. Its range is exactly its
fixed-point set, so a measurable section in a second-countable Hausdorff
base has a Borel range. Each g has exactly one gamma in Gamma such that
g*gamma lies in that range, including the chosen boundary representatives.

## A strict Borel domain with compact closure

Assume G is locally compact and Polish, Gamma has discrete inherited
topology, and G/Gamma is compact. F39 supplies a compact covering set K.
The original Gamma is countable. Enumerating Gamma and selecting the
first right correction placing a given point in K gives a measurable
reduction map. Applying it to the already constructed section preserves
right-coset invariance and yields a measurable section whose range lies
in K.

Thus a Borel set S with compact closure is constructed, satisfying

    for every g in G, there exists a unique gamma in Gamma with g*gamma in S.

This is a strict fundamental-domain statement, not merely a compact
covering statement with overlaps. It does not show that the boundary of
S is null, piecewise smooth, or admits a neighborhood estimate of order t.

## The specified original observation remains unchanged

`quotient_observation_measurable` concerns any given original section c
whose representative map is measurable. It proves measurability of the
actual phase F(gamma_g), retaining gamma_g = g^{-1}*c(g), by joint
evaluation on the finite-dimensional space of original continuous
functions. The exponential then descends measurably through the actual
quotient. The base projection and every measurable base cutoff of this
same observation are also measurable.

The actual H action on its quotient is measurable, using the previously
proved topological group structure and the quotient measurable structure.
F40's global cutoff integral theorem can therefore be applied without
assuming measurable action or a.e. strong measurability of the cutoff
observation separately. Its remaining analytic premises are an actual
invariant finite measure, a measurable specified original section, and
a measurable pointwise bounded base cutoff.

The separately constructed Borel section is an existence result. It is
not silently substituted for a previously specified section, bracket
formula, original model, frequency field or response. To use the paper's
specified canonical section for quantitative boundary analysis, that
section must be matched to its actual geometric construction.

## The actual observation quotient is Borel

The original pointwise topology of finite-dimensional V is Polish and
locally compact. The product homeomorphism gives the corresponding
properties for H when the base has them. A discrete actual Gamma_H is
closed, and the possibly nonnormal quotient H/Gamma_H is Hausdorff.
Its measurable quotient structure equals its topological Borel structure.

`observation_borel_domain_of_presentation` composes these conclusions with
the literal rational polynomial basis, continuous coordinates whose Gamma
image is the full integer grid, and the locally compact Polish base with
discrete cocompact Gamma. It returns the Borel quotient and a strict Borel
fundamental domain of the actual H with compact closure, constructing the
lattice, topology and domain conclusions internally. It does not construct
the full rational Malcev presentation or uniform height estimates.

## Remaining proof obligations

An invariant probability measure on the full original H/Gamma_H is not
constructed in F41. The strict Borel domain now supplies a route via
restriction and pushforward of an actual ambient Haar measure. Its finite
positive mass, normalization, and full H invariance still need to be
proved with the necessary ambient translation-invariance hypotheses.
Those hypotheses must be discharged for the original H; they cannot be
introduced as a new axiom or relabeled as an exempt external deep result.

The specified canonical section's controlled geometric boundary, cutoff
and majorant Lipschitz estimates, and resulting orbit-visit estimates
remain open. Measurability and compact closure alone do not imply them.
Full rational Malcev/Lie data and uniform heights, general rational
descents and uniform termination, and original-frequency structural
extraction/realization are still required for P0.

The complete build and every explicit theorem's transitive axiom audit
are recorded by `python verify.py` in `verification/result.json`. Exact
theorem statements and hypotheses, rather than the number of passing
declarations, determine the scope established here.
