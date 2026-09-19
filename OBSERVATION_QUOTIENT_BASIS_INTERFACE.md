# F38: actual adapted integer bases and real quotient coordinates

F39 update: qualitative cocompactness of the original observation lattice
is now proved under the explicit base and rational-presentation hypotheses
in OBSERVATION_COCOMPACT_INTERFACE.md. The scope below describes F38.

P0 and WeightedCapture remain unproved. This checkpoint adds 33 theorems
to the internal observation-module construction. It proves the qualitative
adapted-basis and quotient-coordinate steps in Section 4 of
`../GMZ_P0_Arxiv_Paper/sections/04-freezing.tex`, especially
`eq:module` and `eq:quotient-coefficients`. No new external deep input or
project axiom is introduced. Uniform height bounds are not proved here.

## Exact objects and scope

Write L = V_Z for the original integer-valued observation subgroup, and
I = W cap L as a submodule of L. `observationIntegerDifferenceModule` uses
exactly the carrier already defined by `observationIntegerDifference`.
The integer quotient is L/I, while the real quotient is V/W. They remain
different objects throughout the argument.

The map L -> V/W has kernel exactly I. Its induced map L/I -> V/W is
injective. This proves that L/I is torsion-free, rather than assuming that
property or cancelling an integer on the circle. Finite generation of L,
supplied by F37's actual subgroup evaluations, gives a finite integer basis
of L/I. Freeness supplies an integer-linear section into the original L.
The section and the original inclusion identify L with I times L/I and
construct an actual adapted integer basis. No basis-height bound is inferred.

The exact quotient Z/2Z has a nonzero class killed by 2 and admits no additive
section into Z. `IntegerQuotientObstruction.lean` checks both claims. This
shows why a general integer quotient could not replace the kernel calculation
above. It is an exact counterexample to a dropped hypothesis, not a finite
test offered as evidence for a general theorem.

## Integer bases really extend to real bases

Integer independence alone does not imply real independence in an arbitrary
real vector space. Here, finitely many actual Gamma evaluations determine V
and send every vector of L to an integer vector. Integer independence passes
through the injective integer evaluation map. Scalar extension of that
integer matrix to R gives real independence of its columns, and hence of the
original functions.

For any finite integer basis of L, its real span is exactly the real span
of L. Once F37's full-span conclusion is applied, the same basis vectors
form a real basis of V. Their number equals dim_R(V). The real coordinates
of every original integer observation equal the casts of its integer
coordinates; the carrier and representatives are unchanged.

## Rationality gives the correct real difference space

Suppose the supplied actual finite real basis b has rational polynomial
representatives P_i in the actual coordinate map. Every rational combination
of b then has an explicit rational polynomial representative. If all Gamma
coordinates are integral, denominator clearing puts a positive integer
multiple of this vector in L.

If W is rational relative to this same b, the argument applied to its actual
rational generators proves

    span_R(W cap L) = W.

Thus the left part of the adapted integer basis spans the original W over R.
It is not merely an integer basis of an unspecified smaller intersection.

`observation_adapted_bases_of_matrix` combines these arguments with F36's
coefficient-span theorem. Its inputs are a literal rational polynomial basis,
the exact integer-grid coordinate image of Gamma, surjectivity of the real
coordinate map, and a literal rational polynomial matrix for the actual
translation differences. Its outputs are compatible actual adapted integer
and real bases. Rationality of W, saturation, quotient freeness, and the
existence of adapted bases are not separate unproved premises in this theorem.

Constructing this full coordinate presentation from general rational Malcev
data remains core work. The resulting basis depends on fixed presentation
data, but this existence proof supplies no uniform rational-height estimate
or finite enumeration of possible bases.

## The original observation's quotient coefficients

Let b_R have left part spanning W and right vectors B_j in the original L.
The actual real-linear map a reads its right coordinates. The checked results
give kernel(a) = W, surjectivity over R, and the exact decomposition

    F = F_W + sum_j a_j(F) B_j,    F_W in W,

for every actual F in V. On L, these coordinates are integer-valued and every
integer coordinate vector is attained by an actual integer combination of
the B_j. There is no discarded residue or root branch.

For a finite polynomial expansion in the original variable,

    F(y) = sum_{d=0}^D y^d A_d,

each quotient coordinate has the exact expansion

    a_j(F(y)) = sum_{d=0}^D y^d a_j(A_d).

This checks preservation of the displayed degree bound. It does not construct
the original nilpolynomial model or prove general structural freezing.

## Remaining interfaces and verification

Still open are uniform bounds for adapted bases and character data, the full
rational Malcev/Lie presentation, group lattice cocompactness, observation
boundary estimates, general rational descents and uniform termination, and
the structural extraction/realization needed for original-frequency capture.
The qualitative adapted-basis gap from F37 is discharged under the exact
presentation hypotheses; its quantitative part remains open.

Original functions, complete responses, weights, full-label distance and
circle branches are unchanged. The historical twelve invalid composite
applications remain unused; no closure of U0 or P2-CSE is asserted.

Run `python verify.py` for the root build and the audit of all explicit theorem
declarations. `verification/result.json` continues to record both main
targets as NOT_proved. Checked conditional statements are not reported as
an unconditional proof of the manuscript or P0.
