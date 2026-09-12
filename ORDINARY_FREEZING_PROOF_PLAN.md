# Ordinary polynomial freezing: internal chain completed at F32

F32 proves MonomialDenseReturns, including m=D, and substitutes it into the
checked degree induction. The complete ordinary theorem in every fixed degree
now has only the two explicit external Weyl premises. This document retains
the staged plan as history; the current exact boundary and proof are in
MONOMIAL_RETURNS_INTERFACE.md. Next work concerns the general structural
models, realization and rational descents.

This document separates the checked D=0 and D=1 core stages from the remaining
plan for higher degrees. F26-F28 preserve the exact original response, affine
relations, actual finite children and Fourier energy. F29 proves the remaining
horizontal argument and complete degree-zero/affine freezing conditional on
CubicTwoCoefficientWeylInput. The external input itself and its library
adaptation are not proved. See CONSTANT_FREEZING_INTERFACE.md.
Its source is the
ordinary-polynomial starting case in sections/04-freezing.tex of the manuscript,
together with the Weyl and return statements in sections/02-preliminaries.tex.
F25 has checked the required finite original-block phase estimate and successful
lags; see WIDE_BLOCK_INTERFACE.md.

F26 now proves the D=1 coefficient identities, both actual block directions,
the bounded-multiplier return steps in k and h, the N^(-5) slope relation,
and the no-relation compressed-block count and operator estimate. Its cubic
Weyl step reuses the project's proved theorem and adds no external input.
See AFFINE_FREEZING_INTERFACE.md for the exact uniform statements.
F27 completes the actual D=1 child construction and its freezing assembly,
conditional only on the explicit degree-zero core proposition. See
AFFINE_CHILD_INTERFACE.md. The workflow below remains incomplete for higher
degrees. The D=0 and D=1 internal arguments are now complete under the explicit
external-input convention. F30 defines genuine full-integer ordinary profiles
and proves their exact double phases and coefficients. From
PolynomialLeadingWeylInput it derives the current-row single-block relation
at N^(-(D+3)) for every D>=2. F31 constructs actual lower-degree children
and connects the complete degree induction conditional on the still-unproved
INTERNAL core statement MonomialDenseReturns. Items 1--5 below are checked
with the explicit external boundary in item 4. Item 7 is constructed and
item 8 is checked conditional on item 6. At F31 the sole remaining internal
lemma was item 6. F32 proves it without any unproved premise.
See ORDINARY_DESCENT_INTERFACE.md and MONOMIAL_RETURNS_PROOF_PLAN.md.

1. Define genuine full-integer polynomial profiles, with degree bounded by D
   and arbitrary real coefficients for each original horizontal x. Their
   restrictions must agree exactly with the original finite profile. Attach
   the ordinary polynomial in r to wideDoublePhase, by an exact evaluation
   identity. An arbitrary agreeing extension has no automatic polynomial type.

2. Prove the coefficient identities. For D>=2 the degree-(D+2) coefficient is
   -3*k*(2*h)^D*a_D(x+h), independently of the successful root y. For D=1,
   prove the two cubic coefficients -2*h*k*(a+3*b) and 2*h*k*(3*a+b).
   The current PhaseAlgebra identities alone do not identify these as
   coefficients of the actual finite-block phase.

3. Use the already checked blockGramKernel_energy_bound_symm on the actual
   masked response kernel. It transfers failure of a block bound to the
   reversed original compressed block. Apply F25 separately in both
   directions. Do not assert adjoint equality of the rectangular widened
   blocks, or intersect independent successful-lag/root sets without proof.

4. State the exact specialized one-variable Weyl input, including a common
   bounded positive multiplier, coefficient convention, actual integer
   interval, and the original N normalization. Its constants and threshold
   must precede N and all real polynomial coefficients. Its external proof is
   outside the present work phase for the general-degree external theorem.
   F26's cubic instance is already proved internally. Any remaining external
   interface must be an explicit
   hypothesis, not a new axiom or an assertion that the input is established.

5. Pigeonhole the bounded multiplier on the actual successful lag set. The
   affine return estimate in k should give a bounded n with
   ||n*h^D*a_D(x)|| <= C*N^(-(D+3)). For D=1 use the two separate directional
   relations, multiply and subtract with the exact factor 8. Earlier checked
   affine-return results may be reused only after matching their hypotheses
   and retaining every denominator and density loss.

6. From many actual large horizontal blocks, pigeonhole n, then prove the
   required degree-D monomial return estimate in h. Its output scale must be
   N^(-(2*D+3)), with constants before N and the coefficients. The manuscript
   includes the critical m=n case in the general return lemma; finite tests
   cannot replace this general argument. The affine result alone does not
   cover all D.

7. Use the true top-coefficient relation to build every rational residue and
   remainder-grid branch. On y in [N^2], the small top-coefficient remainder
   becomes a circle error of order N^(-3). Construct the actual finite list
   of degree-(D-1) profiles and its pointwise assignment; do not presume a
   uniform list exists. Retain all residue and circle-root branches.

8. Match the output to F23's compressed-block count and F24's freezing-step
   theorem, with the child count and error budget in the manuscript's order.
   This requires a degree induction and uniform Q,N0, not merely a conditional
   one-step implication.

The D=0 starting case has its own vertical Fourier argument. F28--F29 prove
its finite cyclic realization and exact passage back to the original response,
using both cubic and quadratic coefficients and bounds uniform in the vertical
Fourier parameter. Its explicit premise is CubicTwoCoefficientWeylInput;
the general leading-coefficient premise alone does not replace it.

These obligations concern the manuscript's core proof. The deeper structural
observation case, realization, rational descents and their termination remain
separate obligations. Neither this plan nor F25 establishes P0 or WeightedCapture.

## Actual constant children on affine relation rows: completed at F27

F26 supplies Q,E,N0 for the affine no-relation estimate. Here Q is a slope
multiplier bound, not the final major-arc cutoff. On a relation row select its
actual 1<=q<=Q and a nearest real lift u of q*a(x), with |u|<=E/N^5. Retain the
actual j in {0,...,q-1} in a(x)=(u+j)/q mod 1. For an original y in [N^2],
j*y/q has one of all q residues and |u*y/q|<=E/N^3.

For a requested circle accuracy epsilon/(2*N^3), rounding the latter real
remainder to a grid with spacing epsilon/N^3 uses only boundedly many integer
indices t, depending on E and epsilon. The proposed constant-in-y children are

    b(x) + j'/q + t*epsilon/N^3  mod 1,

F27 implements this through the existing major-arc grid with R=max(Q,ceil(E)),
keeping every 1<=q<=R, every j' in {0,...,q-1}, and every retained bounded t.
The common index set and its cardinality must precede N,a,b; the children may
depend on N and the original intercept field b. A pointwise assignment is
required only on actual relation rows, but each child formula is globally
defined on the original box. This construction is now proved in AffineChildren.

AffineFreezing now connects the child list and its exact approximation to F24's
three-piece estimate with the same original input, parent-minor mask, child
error s/(3*sqrt(J)), and all major-arc transfer conditions. F29 supplies the
degree-zero estimate from CubicTwoCoefficientWeylInput and thereby completes
the internal affine argument under the external-input convention.
