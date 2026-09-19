# F43: unique original quotient probability and exact base marginal

Historical checkpoint. F44 constructs exact triangular half-open coordinate
cells and identifies every specified original section taking values in
that same cell. It also proves local constancy of the original correction
above interior representatives and local continuity of the original
observation pullback. See CANONICAL_COORDINATE_SECTION_INTERFACE.md for the
current scope and remaining quantitative/domain-matching obligations.

P0 and WeightedCapture remain unproved. This checkpoint adds 18 theorem
declarations in three modules, closing the invariant-probability uniqueness
and base-marginal identification interfaces left by F42. The original
observation, specified section, lattice, frequency field and responses
are not changed. The complete build and transitive axiom audit are recorded
in `verification/result.json`.

## Counting the original fibers

For a locally compact Polish group G with its Borel structure, an actual
discrete subgroup Gamma, and compact G/Gamma, F41 constructs a bounded
measurable section. Here it descends to a genuine right inverse s of the
original quotient map, with all values in a fixed compact K.

For any measure mu on G/Gamma, its counting lift is

    M = sum over gamma in Gamma of map(x -> s(x)*gamma, mu).

Periodization along the actual lattice gives the precise integral formula
for M. Left multiplication by a in G permutes every original fiber:

    a*s(x)*gamma = s(a*x)*(delta(a,x)*gamma),  delta(a,x) in Gamma.

The proof retains this correction and reindexes by an actual bijection
of Gamma. Full G invariance of mu therefore gives left invariance of M.
No normality or replacement of G/Gamma by a group quotient is used.

The strict domain is D = {g : s(g*Gamma)=g}. It is Borel, and s(x)*gamma
belongs to D exactly when gamma=1. Restricting M to D and applying the
original quotient map consequently recovers mu exactly, for all Borel
sets. In particular M(D)=mu(G/Gamma).

If mu is finite, M is finite on every compact C. Indeed any lattice element
contributing a point s(x)*gamma in C belongs to K^(-1)*C. Its intersection
with the closed discrete original Gamma is finite. The actual counting
sum over C thus reduces to finitely many finite measure terms. Local
finiteness is proved, not added as a premise.

## Uniqueness with the correct normalization

For two full G invariant probability measures, use the same auxiliary
bounded section and lift both. Ambient Haar uniqueness identifies each
lift with a nonnegative scalar multiple of a fixed Haar measure. Both
lifts give D mass one; D is contained in K, so its Haar mass is finite,
and the mass-one identity proves positivity. Cancelling this finite
positive mass identifies the two scalars. Exact recovery on D identifies
the original quotient measures.

`compact_quotient_invariant_probability_unique` proves this for the actual
possibly nonnormal quotient. Probability normalization is essential to this
statement: arbitrary scalar multiples of an invariant measure are still
invariant. No uniqueness is asserted without matching total mass.

The auxiliary s appears only in this proof of measure uniqueness. It is
never substituted for the paper's specified canonical observation section.

## The original observation projection

The actual projection pi:H/Gamma_H -> G/Gamma satisfies

    pi(a*x) = a.base * pi(x).

The original base inclusion g -> (g,0) then proves that the marginal of
every full H invariant measure is full G invariant. If the measures are
probabilities, the proved uniqueness identifies this marginal with every
specified full G invariant base probability. The result is an actual
`MeasurePreserving` statement for the original projection, not an assumed
integral identity.

`observation_measure_identification_of_presentation` builds the topology,
discrete lattice and compact quotient from the literal rational polynomial
basis, continuous coordinates with full integer-grid subgroup image, and
the locally compact Polish base with discrete cocompact Gamma. It concludes
existence and uniqueness of full H invariant probability and identifies
its original base marginal. This also identifies the measure used in F42
with any separately specified full H invariant probability.

## Remaining core work

The paper's particular half-open canonical section must still be connected
to its actual coordinate construction, with measurability and controlled
boundary geometry. Arbitrary compactly contained Borel domains do not give
O(t) boundary neighborhoods or O(1/t) Lipschitz cutoffs. Those estimates,
their majorants, and the actual orbit-visit argument remain open.

Identification here applies to measures already proved to be invariant
probabilities. If a coordinate-defined candidate measure has not yet been
shown to have those properties, that verification is still required; the
uniqueness theorem cannot establish its hypotheses.

Full rational Malcev/Lie presentations and uniform height bounds, general
descents and uniform termination, original-frequency extraction and
realization, and final WeightedCapture/P0 assembly remain open. External
deep results keep their earlier explicit-premise status. No new external
deep premise or project axiom is introduced.
