# F29: degree-zero and affine freezing from the explicit Weyl input

The internal degree-zero argument is now checked through the actual Gram
kernel, coefficient returns, large-entry count, Schur estimate and F28 Fourier
passage. Complete affine freezing follows using F26-F27's proved no-relation
estimate and constructed children. Both results are conditional on
CubicTwoCoefficientWeylInput, stated in GMZP0/ConstantFreezing.lean.

That analytic proposition is a function premise, not an axiom or a proved
theorem. No separate degree-zero or horizontal core estimate is assumed in
the final theorems. This checkpoint does not prove P0 or WeightedCapture.

## The external input and its source boundary

For each v>0 the input supplies positive D,C,N0 before N, both interval
endpoints and all four circle coefficients. If N>=N0, 1<=L, U<=N and

    v*N <= |sum_{r in [L,U]} e(a3*r^3+a2*r^2+a1*r+a0)|,

then there is one positive integer q<=D such that

    ||q*a3|| <= C/N^3,    ||q*a2|| <= C/N^2.

The denominator is common to the two coefficients. The interval length does
not replace the original N in this statement. Empty intervals cannot satisfy
its positive lower bound. All coefficients remain in R/Z.

The manuscript's equation (weyl), in sections/02-preliminaries.tex, states
the all-coefficient version. The primary source checked on 2026-09-12 is
[Green and Tao, Proposition 4.3](https://arxiv.org/html/0709.3562v6#S4).
It supplies a common multiplier controlling the polynomial's C-infinity
norm; Lemma 4.4 alone only controls the leading coefficient. The input above
is an adapted corollary, not a literal transcription of Proposition 4.3.
Its adaptation uses the exponential as an equidistribution test, interval
length at least v*N, integer translation, and conversion of binomial to
ordinary coefficients with a fixed factorial multiplier. Those adaptations
and the external theorem are not formally derived here. The checked core
therefore claims an implication from exactly the displayed analytic input.

## Exact core chain

horizontalCubicKernel_action identifies the finite kernel with the genuine
horizontal Fourier response, on exactly Fin(2*N). Shared horizontal inputs
are in bijection with the full blockLabels interval I_h. No boundary label
is suppressed. The Gram diagonal is exactly 1/N and every entry has norm
at most 1/N.

The actual phase is

    a*r^3 - b*(r-h)^3 + xi*(2*h*r-h^2).

Its four ordinary coefficients are, from highest to lowest,

    a-b, 3*h*b, -3*h^2*b+2*h*xi, h^3*b-h^2*xi.

The formula, original N^(-2) Gram normalization and actual interval endpoints
are checked. A Gram entry larger than v/N gives a complete sum larger than
v*N. The external input therefore applies to this actual phase.

Multiplying the cubic relation by 3*h and adding the quadratic relation
proves the current-row return

    ||(3*q)*(h*a)|| <= 4*C/N^2,    |h|<=N.

The original current-row frequency a is retained. An exact nonzero-frequency
example shows why vanishing a-b alone cannot replace the two relations.

Many actual off-diagonal large entries yield a set of distinct signed
displacements in [-N,N], with exactly the same cardinality. The proved
bounded-multiplier affine-return theorem is applied at exponent 2. This
produces ||q'*a||<=E/N^3 with uniformly bounded positive q'. Taking the final
cutoff at least both the denominator bound and ceil(E) gives genuine
MajorArc membership of the original current-row frequency.

Contrapositively, a minor row has fewer than rho*N large entries for every
xi. Scalar Schur retains the diagonal 1/N, the small-entry budget v, and
the large-entry budget rho. The resulting squared-energy coefficient is
rho+v+1/N, not its square. The F28 passage returns to the same original input
and complete response. Arbitrary horizontal contractive masks are handled
on their actual support; no vertical mask is Fourier-diagonalized.

## Uniform constants and conclusions

Given s>0, first choose positive rho,v and a numerical threshold with
rho+v+1/N<=s^2. The Weyl constants are then chosen from v, and recurrence
constants from rho and the Weyl bounds. Their maximum scale and final
major-arc cutoff precede N, every horizontal coefficient field and xi.

The final checked theorems are

    uniform_horizontal_constant_freezing_of_weyl
    uniform_constant_freezing_of_weyl
    uniform_affine_freezing_of_weyl

Each explicitly requires CubicTwoCoefficientWeylInput. For every 0<s<=1,
the affine conclusion supplies Q,N0 before N,a,b, and proves the original
FiniteMinorEstimate for a(x)*y+b(x), with unrestricted horizontal dependence.
The F27 child count, all rational/root branches and original assignments
remain intact. No parameter is chosen from the original input function.

## Remaining work

Under the user's requested external-input convention, the internal D=0 and
D=1 freezing arguments are complete. Unconditional library-backed versions
still require a proved witness of the exact Weyl input, which is not part of
the current external-deep-theorem proof phase. F30 proves the higher-degree
ordinary coefficient formulas and single-block relation under an explicit
leading Weyl premise. F31 constructs genuine ordinary children and connects
degree induction conditional on MonomialDenseReturns; F32 proves that lemma
and completes the ordinary internal chain. General structural models still need their output types, realization,
forced relations, rational descents and uniform termination. The strong capture
and P0 targets remain unproved.

The 31 new theorem declarations are in HorizontalCubicKernel.lean,
ConstantGramPhase.lean, HorizontalSchur.lean and ConstantFreezing.lean.
They are included in the root build and exhaustive transitive-axiom audit.
The historical twelve erroneous three-dimensional applications stay unused;
general P2-CSE and U0 remain open and unchanged.
