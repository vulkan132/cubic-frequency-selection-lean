# F39: the original observation lattice is discrete and cocompact

F40 update: normalized Haar probability and genuine mean-zero integrals
on the original additive fiber are now proved under the explicit rational
presentation and constant-one membership. The global integral result is
conditional on an actual invariant finite measure and measurability; see
OBSERVATION_FIBER_MEAN_INTERFACE.md. The scope below describes F39.

P0 and WeightedCapture remain unproved. F39 adds 14 theorem declarations
for the qualitative lattice step following `eq:semidirect` in Section 4
of `../GMZ_P0_Arxiv_Paper/sections/04-freezing.tex`. No new external deep
premise or project axiom is introduced. The rational coordinate presentation
is still an explicit input, not something F39 constructs from Malcev data.

## Exact hypotheses of the integrated theorem

`observation_group_lattice_of_presentation` assumes:

- G is a locally compact topological group.
- Gamma is an actual subgroup with discrete inherited topology, and G/Gamma
  is compact in the quotient topology.
- V is the original translation-invariant observation module.
- A finite real basis b of V is given by actual rational coordinate
  polynomials: b_i(g) = P_i(coord(g)) for every i and every g.
- The coordinate map is continuous. Its image on Gamma is precisely the
  full integer grid: every Gamma point has integer coordinates, and every
  integer coordinate vector occurs at an actual Gamma point.

It proves that the original H is a topological group, the original
Gamma_H is discrete, and H/Gamma_H is compact. The theorem constructs the
needed compatible integer and real bases using F37--F38 and derives the
compact covering set from compactness of G/Gamma. Neither an integer basis
nor a compact fundamental domain is an additional hypothesis.

Here H has the exact multiplication

    (g,P)(h,Q) = (gh, P composed with L_h + Q),
    Gamma_H = Gamma times V_Z.

The quotient identifies a with a*l for l in Gamma_H, hence its cosets
are a*Gamma_H. No normality is assumed and no quotient group structure
is used for H/Gamma_H.

## Constructive reduction inside the original objects

For compatible bases b_Z and b_R, rounding the real coordinates of F
produces the actual element

    Z(F) = sum_i floor(b_R.repr(F)_i) * b_Z(i) in V_Z.

Every coordinate of F-Z(F) lies in [0,1). The closed cell with coordinates
in [0,1] is compact in V's actual pointwise subspace topology. Its image
under the additive quotient map covers all of V/V_Z, proving compactness.

For the base, local compactness supplies a compact neighborhood C of the
identity. The images of g*interior(C) form an open cover of G/Gamma.
A finite subcover gives a compact set K meeting every coset. Thus for
every g there is an actual gamma in Gamma with g*gamma in K. This does
not use a global continuous section.

For a=(g,F), choose such a gamma and round the translated observation
T_gamma(F), obtaining Z in V_Z. Right multiplication by l=(gamma,-Z)
gives exactly

    a*l = (g*gamma, T_gamma(F)-Z).

This belongs to K times the closed fiber cell. The product is compact in
the actual topology of H, and its quotient image is the entire H/Gamma_H.
The lattice itself is homeomorphic, with inherited topologies, to
Gamma times V_Z; the factor discreteness therefore proves its discreteness.

The order of the correction matters. F33's exact affine counterexample
already checks that omitting the pullback changes the circle phase by 1/2.
F39 retains that pullback before rounding. It does not change the original
observation, frequencies, responses or root branches.

## Scope that remains open

The closed cell is a compact covering cell; its boundary can overlap.
F39 does not prove uniqueness or regularity of a chosen representative,
construct normalized Haar measures, prove the observation's fiberwise
mean-zero integral, or prove boundary neighborhood and Lipschitz estimates.
No bound on the diameter or height of the constructed basis or covering
set is asserted. It also does not construct a Lie structure, exponential
and logarithmic coordinate formulas, or a bounded rational Malcev basis.

The principal remaining interfaces are the uniform quantitative rational
presentation and character bounds, observation boundary analysis, general
rational structural descents with uniform termination, and the passage
from original frequency data to the required structural models. These
must be connected to the already proved conditional capture and P0
reductions. External deep inputs retain their explicit premise status.

## Verification

The four added modules are `ObservationCompactCell`,
`ObservationGroupCompact`, `CompactQuotientCover` and
`ObservationLatticeCocompact`. All 14 explicit theorem declarations are
included in the main import and transitive axiom audit. The complete
verification command is `python verify.py`; authoritative output is in
`verification/result.json`. Kernel checking establishes the declared
theorems; it does not replace checking that their hypotheses match the
paper or establish the remaining P0 interfaces.
