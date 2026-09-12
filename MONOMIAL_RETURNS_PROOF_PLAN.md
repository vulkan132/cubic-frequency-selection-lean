# Dense monomial returns: F31 plan, completed at F32

F32 proves MonomialDenseReturns with no unproved premise and substitutes it
into ordinary freezing. See MONOMIAL_RETURNS_INTERFACE.md for the checked
proof and exact constants. The original plan below is retained as history.
The implementation uses rational interpolation over finitely many relative
node patterns for the uniform integer seed. Its same-sign rounding-fiber
argument uses (y-x)^D<=y^D-x^D, so no deletion near zero or derivative estimate
is needed. The next core work concerns general structural models and descent.

F31 isolates this unproved INTERNAL lemma as MonomialDenseReturns. It is not
covered by the user's exemption for external deep theorems. The exact source
is sections/02-preliminaries.tex, Lemma (Dense returns), lines 58--99 in the
current manuscript. Read the source and Lean proposition when implementing;
do not reconstruct the quantifiers from a conversation summary.

The ordinary induction only consumes m=D+3. The general structural argument
also needs the critical m=D case, which the proposition explicitly includes.
The coefficient is in R/Z, the retained integers are actual distinct nonzero
points, and the original N remains in every denominator.

## Counterexample checks before a proposed proof

- q*a small does not make a small: retain the positive multiplier and all
  integer circle branches. F31's exact half-frequency obstruction applies.
- The affine return result covers D=1. It cannot be applied to the image
  h^D as though that image had positive density in [-N,N]. Its diameter is
  of order N^D and even powers also identify opposite signed h.
- A close cluster alone gives only N^(-m), not N^(-(m+D)). The amplification
  needs many original returns across a macroscopic range.
- Do not use a derivative lower bound near h=0. First retain one sign and
  delete a controlled interval of small |h|, accounting for the integer +1.

## 1. Uniform seed from a short cluster

Partition a one-sign interval into integer intervals of bounded length L.
For N above an explicit threshold, density forces D+1 distinct good integers
in one such interval. All choices of L and the threshold precede N and a.

The leading-coefficient cofactors of their Vandermonde matrix give integers
c_i and a nonzero integer q with sum_i c_i*h_i^j=0 for j<D and equal to q
for j=D. The relevant cofactors depend only on pairwise differences; using
arbitrary cofactors with absolute-position bounds would lose uniformity.
Bound their absolute values by powers of L, retain |q|, and apply the circle
triangle inequality to obtain ||q*a||<=C0/N^m with 1<=|q|<=Q0.
Mathlib polynomial interpolation or determinant identities may supply the
algebra, but the actual bounded integer multipliers must still be constructed.

Choose a nearest real lift u of q*a. Then |u|<=C0/N^m and every original
good h still has ||u*h^D||<=Q0*C/N^m. This uses multiplication on R/Z,
not choosing a zero root for a.

## 2. Amplification using actual rounding fibers

Retain a positive proportion with one sign and |h|>=c_rho*N. With m>=D
and N>=1, |u|*N^D<=C0. Thus rounding u*h^D to its nearest integer gives
only boundedly many integer fibers, uniformly before N and the original data.
Pigeonhole the actual fiber; its cardinality is a positive multiple of N.

For two sufficiently separated retained positive integers h1<h2 in that
same fiber, the real difference is bounded by 2*Q0*C/N^m. Algebra gives

    h2^D-h1^D >= (h2-h1)*h1^(D-1).

This follows by factoring the power difference, with all summands nonnegative.
The cardinality of the fiber forces h2-h1>=c'*N once the threshold absorbs
the integer +1. The lower bound h1>=c_rho*N then forces
|u|<=E/N^(m+D). For a negative retained sign, explicitly account for parity
before converting it to positive integers. The case u=0 is immediate.

This finite rounding-fiber route proves the same amplification as the
manuscript's derivative-and-interval-count argument while avoiding a
continuum mean-value wrapper. Existing AffineReturnAmplification and finite
diameter/counting lemmas may be reused only with their exact hypotheses.
This is a plan, not a proof or a claim that all required library lemmas exist.

## 3. Integration and proof boundary

Produce a witness of MonomialDenseReturns with no unproved core premises.
Then substitute it in uniform_ordinary_freezing_of_returns. The bounded
multiplier fiber, actual block count, no-relation operator, genuine children,
all-degree induction and same original response are already connected by F31.
The two external Weyl inputs remain explicit under the user's current scope.
General structural model construction, rational descents and termination
remain separate core tasks even after ordinary freezing is completed.
