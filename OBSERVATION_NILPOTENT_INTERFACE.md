# F35: actual commutators, nilpotence and continuous characters

P0 and WeightedCapture remain unproved. This checkpoint proves core parts of
Section 4 of the manuscript, without a new external input or project axiom.
The source is `../GMZ_P0_Arxiv_Paper/sections/04-freezing.tex`, specifically
the equations labelled `semidirect`, `commutator`, `horizontal-H` and
`H-curve`. The original Phase 12 and Phase 30 contracts were reread; their
original-response, full-label and circle-root requirements are unchanged.

## Exact commutator subgroup

For any group G and actual translation-invariant real function module V,
write T_g P(u)=P(g*u), and W=span_R{T_g P-P}. The previously constructed
group has multiplication (g,P)*(h,Q)=(g*h,T_h P+Q).

`observation_commutator_eq` proves, as an equality of actual subgroups,

    [H,H] = {(g,P) : g belongs to [G,G] and P belongs to W}.

This is a statement about the pairs and their semidirect multiplication;
it does not assert an isomorphism with a direct product group.
Every full commutator's observation coordinate is calculated with all four
noncommutative translation factors. The reverse inclusion uses

    [(g^(-1),0),(1,P)] = (1,T_g P-P).

The passage to the REAL span is proved explicitly: multiplying P by any
real t realizes t*(T_g P-P) as another actual commutator. Span induction
then uses finite products in the identity-base fiber. Neither topological
closure nor an assumption that a subgroup is a real subspace is used.
Base commutators enter through the genuine base inclusion, and each pair
factors in the base-then-fiber order.

## Nilpotence with a uniform bound

For an actual flag U_n in V with U_0=0, U_K=V and

    T_g P-P belongs to U_n whenever P belongs to U_(n+1),

the lower central series of H projects to the lower central series of G.
If the latter vanishes at c, the former lies in the full observation fiber
at c. Each additional commutator lowers its fiber by one flag level:

    lowerCentralSeries(H,c+n) <= fiber(U_(K-n))  for every n<=K.

Consequently it vanishes at c+K. This is the actual group lower central
series, not an assumed nilpotent structure or a Lie-algebra surrogate.

`observation_nilpotent_of_triangular` supplies the F34 flag directly.
Its hypotheses are: G is nilpotent; m real coordinates obey the exact
left-translation substitution formula; every correction uses only lower
coordinates and has ordinary degree at most D; every actual member of V
has an evaluated polynomial representative of ordinary degree at most R.
It concludes

    class(H) <= class(G) + R*(D+1)^m + 1.

The bound precedes all real coefficients and translations. This theorem
does not assume V nonconstant or that it contains 1. Those additional
hypotheses enter the separate F34 proof of 1 in W and W proper.
Matching a full rational Malcev presentation to these exact coordinate
hypotheses remains a necessary interface.

## Actual continuous characters and the source term

An arbitrary group homomorphism chi:H -> (R,+) restricts to a base
character eta and an additive fiber map. Its actual fiber restriction
annihilates the entire W by the commutator result, not just the individual
translation generators. Its values are translation invariant.

For continuous characters we place on H the actual product topology of G
and V, where V carries the pointwise subspace topology in (G -> R).
The two inclusions are proved continuous. The fiber restriction is
continuous and hence real-linear, using Mathlib's proved continuous
additive-map theorem. `observation_continuous_character_form` gives

    chi(g,P) = eta(g) + ell(P),   ell(W)=0.

If chi is nontrivial, its base and linear fiber parts are not both zero.
If chi is integer-valued on the actual subgroup Gamma_H, then eta is
integer-valued on Gamma and ell is integer-valued on V_Z. These statements
do not require a yet-unproved full lattice assertion.

Given 1 in W, `observation_continuous_character_curve` applies this to the
same actual curve point already used in the complete original block phase:

    chi(g,source*1-A*T_g F) = eta(g)-A*ell(F).

This holds for every real source and A, every g and every F in V. No
real-linear representative is now an extra hypothesis for a continuous
character. The source term is eliminated exactly, without changing the
original target values, f, lag labels or roots. No division in the circle
or selection of one circle branch occurs in this argument.

The topology construction by itself does NOT prove joint continuity of
the translation action, a Lie group structure, or agreement with a
separately supplied Malcev manifold presentation. Those links, and the
bounded integer bases needed for quantitative character choices, remain
to be proved. An arbitrary discontinuous additive map is never treated
as real-linear.

## Exact obstruction

`observation_abelian_base_obstruction` uses the actual module of affine
real functions over the additive real base. The commutator of the base
element -1 with the coordinate function P(u)=u is the nonzero constant-one
fiber element. Thus abelianness of the base alone does not imply
abelianness of H. This is an exact group identity and nonidentity proof,
not a numerical test or a counterexample to P0.

## Remaining core route to P0

1. Construct and match the rational Malcev presentation, prove W rational
   and V_Z a full lattice, and construct bounded adapted integer quotient
   and character bases. Saturation alone does not supply them.
2. Prove the needed topological/Lie and rational polynomial structure,
   polynomial-curve filtration, and observation fiber mean-zero and
   uniform boundary/Lipschitz bounds. Then connect the precisely stated
   external quantitative equidistribution input.
3. Derive both general relation types from actual large blocks, preserving
   the original roots. Construct all rational descent branches, with the
   retained individual degrees, uniform termination and error budgets.
4. Complete structural extraction/realization for the original theta and
   original positive weight. Supply the actual hypotheses of the checked
   terminal capture theorem, and then use WeightedCapture -> P0.

External deep results remain explicit inputs, outside this work phase,
and are not new axioms. The twelve deferred three-dimensional composite
applications remain unused. P2-CSE and U0 stay open.

## Files and verification

- `GMZP0/ObservationCommutator.lean`: 16 theorem declarations.
- `GMZP0/ObservationNilpotent.lean`: 9 theorem declarations.
- `GMZP0/ObservationCharacters.lean`: 7 theorem declarations.
- `GMZP0/ObservationCommutatorObstruction.lean`: 2 theorem declarations.
- `GMZP0/ObservationContinuousCharacters.lean`: 9 theorem declarations.

F35 adds 43 declarations, for a project total of 1109. `python verify.py`
builds the full project and audits every explicit project theorem's
transitive axioms. Allowed foundations remain propext, Classical.choice
and Quot.sound. The theorem count measures audit coverage, not the
percentage of P0 completed. See `verification/result.json` for the actual
machine result and the explicit unproved status of P0 and WeightedCapture.
