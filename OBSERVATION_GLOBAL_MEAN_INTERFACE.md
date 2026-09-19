# F42: invariant probability and global original-observation means

Historical checkpoint. F43 proves uniqueness among full-group invariant
probabilities and identifies the original base marginal through an actual
measure-preserving projection. See OBSERVATION_MEASURE_IDENTIFICATION_INTERFACE.md
for the current scope, including the distinction between invariant
probabilities and coordinate-defined measures whose invariance is unproved.

P0 and WeightedCapture remain unproved. This checkpoint addresses the
full-quotient measure input left by F40 and F41, at the fixed observation
in Section 4 of `../GMZ_P0_Arxiv_Paper/sections/04-freezing.tex`.
The two modules add eight explicit theorem declarations. The complete
build and transitive axiom audit are recorded in `verification/result.json`.

## Haar right invariance is derived

Let G be a locally compact Polish topological group with its Borel
measurable structure, and let Gamma be an actual discrete subgroup such
that G/Gamma is compact. No normality is assumed. F41 constructs a Borel
set S with compact closure and exactly one right Gamma correction into S
for every point of G.

Inverting S gives a strict left Gamma domain. For each g in G, the
preimage of this left domain under right multiplication by g is again a
strict left domain, pointwise. Left Haar measure is invariant under the
countable original Gamma, so these two left domains have equal measure.
Their common measure is nonzero because countably many translates cover
G, and finite because the domain has compact closure. Haar uniqueness
expresses the right-translated measure as a scalar times the original
one. The finite positive domain mass forces that scalar to be one.

Thus `cocompact_lattice_haar_right_invariant` proves right invariance for
every ambient Haar measure from the original lattice hypotheses. Ambient
right invariance or unimodularity is not an extra unproved premise, a
new project axiom, or an exempt external deep input.

## A probability on the original quotient

The original strict right domain is a fundamental domain for Gamma.op
acting by right multiplication. Restrict the actual ambient Haar measure
to this domain and push it forward by the original quotient map. Its
total mass is exactly the domain mass, separately proved finite and
nonzero. The fundamental-domain quotient measure theorem gives invariance
under the full original G, using the just-proved ambient right invariance.
Normalizing yields a probability measure on the actual, possibly nonnormal
quotient G/Gamma.

`compact_quotient_invariant_probability` performs this construction inside
the proof. A supplied invariant quotient measure is no longer required.
Existence of a measure without proving its invariance, or a zero measure,
would not satisfy its conclusion.

## The actual observation and its exact quantifiers

`observation_quotient_probability_of_presentation` applies the construction
to the original H/Gamma_H, using the literal finite rational polynomial
basis, continuous coordinates with full integer-grid image on Gamma,
and the locally compact Polish base with discrete cocompact Gamma. The
actual H topology, lattice discreteness and compact quotient follow from
the previously proved presentation results.

When V contains constants, `observation_global_mean_zero_of_presentation`
constructs one probability mu, invariant under the full H, before every
choice of the specified measurable original section c and every bounded
measurable base cutoff chi. For all of these c and chi it concludes both
integrability and

    integral chi(base(x)) * quotientObservation(V,c,x) dmu = 0.

It uses the original half-constant action: this fixes the actual base
coset and changes the original observation's sign. No replacement section,
fiber disintegration theorem, frequency lift, root choice, original
function or original response is substituted into this argument.

## Remaining scope

The specific canonical section used by the paper still must be matched
to its actual coordinate construction, including its measurability and
controlled boundary geometry. The existence of the unrelated Borel
section from F41 does not settle that obligation.

This checkpoint constructs an invariant probability, but does not prove
uniqueness among all invariant probabilities or identify its base marginal
with a separately specified canonical measure. Such identifications,
where needed in the boundary and equidistribution interface, must be
proved explicitly. The O(t) boundary-neighborhood bounds, O(1/t) Lipschitz
cutoffs and majorants, and resulting orbit-visit estimates remain open.

Full rational Malcev/Lie data and uniform height bounds, general rational
descents with uniform termination, original-frequency structural
extraction/realization, and the final capture/P0 assembly remain required.
External deep analytic results retain their existing explicit-premise
status. No new external deep premise is introduced at F42.
