# F30: genuine ordinary polynomial phases and single-block returns

For every fixed D>=2, the actual double-phase polynomial and its degree-(D+2)
coefficient are now checked. From the explicit PolynomialLeadingWeylInput,
each actual large compressed block gives a bounded-multiplier return for the
original current-row top coefficient at scale N^(-(D+3)). The nonlinear
return step in the horizontal displacement and complete high-degree freezing
are still unfinished. P0 and WeightedCapture remain unproved.

## Actual profiles and original responses

An ordinary profile is specified by an unrestricted field

    P : Fin N -> Polynomial R,    natDegree(P(x)) <= D for every x.

The full integer profile is eval(P(x),y) modulo one, and the original profile
uses y=label(z.2), exactly as in the original box. Agreement at every original
point and equality of the complete response for the same original f are
proved. Outside-box evaluations are evaluations of this genuine polynomial;
no arbitrary agreeing extension is treated as polynomial.

UniformOrdinaryFreezing(D) records the exact induction target. Its positive
cutoff and scale threshold precede N and all polynomial coefficient fields.
The D=0 and D=1 cases are now connected to the existing F29 results, retaining
CubicTwoCoefficientWeylInput as their explicit external premise.

## Exact polynomial and coefficients

For two real polynomials A,B and real y,h,k, the checked polynomial is

    A(y)*(X+k)^3 - A(y+2*h*k)*X^3
      - B(2*h*X+y+2*h*k-h^2)*((X+k-h)^3-(X-h)^3).

Its evaluation on each integer r is exactly the complete circle phase in
wideDoublePhase. The same identity identifies the actual wideLagSum before
any norm is taken, on the complete lagLabels interval with original N
normalization.

The cubic shift difference is exactly quadratic, with degree-two coefficient
3*k. For any bounded-degree B, affine substitution multiplies its indexed
degree-D coefficient by (2*h)^D. This assertion includes zero slope, the zero
polynomial, zero top coefficient and actual degree below D.

For D>=1 the full phase has degree at most D+2. For D>=2 its degree-(D+2)
coefficient is exactly

    -3*k*(2*h)^D*coeff(B,D).

In the actual profile B=P(x+h), this coefficient is independent of y. The
formula does not require the phase to have exact degree D+2.

The D>=2 restriction is necessary. A checked example with A=X, B=0 and
y=0,h=k=1 has cubic coefficient -2 although coeff(B,1)=0. The earlier affine
argument is retained for D=1. This is an obstruction to a coefficient-rule
misapplication, not a counterexample to P0.

## The explicit external analytic input

PolynomialLeadingWeylInput states that, for each fixed positive degree d and
c>0, positive Q,E,N0 precede N, interval endpoints and every real polynomial
with degree at most d. If the complete sum over an integer subinterval of
[1,N] has modulus at least c*N, an actual positive q<=Q satisfies

    ||q*coeff(P,d)||_(R/Z) <= E/N^d.

This is the leading-coefficient specialization of the manuscript's Weyl
input, in the project's ordinary-coefficient, bounded-degree and original-N
conventions. It is a function premise, not a new Lean axiom or a proved
external theorem. Its conversion from an external library statement is not
proved here. It does not replace the simultaneous two-coefficient input used
for the degree-zero starting case.

## From an actual large block to the current row

F25 gives many nonzero lags and, for each lag, its own actual original source
root. The exact polynomial above is attached to each of these sums. The
external input yields bounded positive Weyl multipliers on the actual lag
set. The checked denominator-fiber and affine-return theorem in k, at
exponent D+2, gives a return at exponent D+3. No roots or successful lag sets
are synchronized.

The fixed factor 3*2^D is absorbed into the positive multiplier and never
cancelled on the circle. The first directional result controls the partner
row's coefficient. Apply it to the reversed original compressed block,
using its proved adjoint-norm equality, to control the current row. The sign
(-h)^D is handled for both parities without changing the norm. This argument
does not assert an adjoint equality for the rectangular widened blocks.

The final theorem uniform_ordinary_block_row_relation states that for fixed
D>=2 and v>0 there are Q,E,N0>0 before N, every original polynomial field,
every contractive pointwise mask and every pair x!=x'. Failure of the actual
compressed v/N block bound implies an actual positive integer n<=Q with

    ||n*h^D*coeff(P(x),D)||_(R/Z) <= E/N^(D+3).

The coefficient is that of the original current row. This statement does
not capture the original pointwise value theta and does not yet give the
uniform no-relation count for higher degrees.

## Remaining core interfaces

Many such actual blocks give many distinct horizontal displacements h. The
nonlinear monomial return estimate upgrades these relations to a bounded
multiple of coeff(P(x),D) at N^(-(2*D+3)). The affine-return theorem alone
is insufficient for D>=2. F32 proves the required monomial estimate internally,
including the critical exponent case, without invoking an external premise.

F31 constructs actual degree-(D-1) child profiles, retaining all rational
residues, circle branches and remainder-grid values, and connects uniform
degree induction with the existing freezing budget. F32 proves the internal
MonomialDenseReturns lemma and completes the ordinary chain from only the
two explicit external Weyl premises. See MONOMIAL_RETURNS_INTERFACE.md.
General structural model realization, rational descents and uniform
termination also remain.

The 26 new theorem declarations are in OrdinaryPolynomialAlgebra.lean,
OrdinaryProfiles.lean and OrdinaryBlockRelations.lean and are included in the
root build and transitive-axiom audit. The twelve deferred erroneous
three-dimensional applications remain unused. P2-CSE and U0 are unchanged.
