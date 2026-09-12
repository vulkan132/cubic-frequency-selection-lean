# F32: proved dense monomial returns and ordinary freezing

The internal MonomialDenseReturns obligation from F31 is now discharged by
monomial_dense_returns. Its proof has no external analytic or unproved core
premise. The ordinary freezing theorem for every fixed natural degree now
has only CubicTwoCoefficientWeylInput and PolynomialLeadingWeylInput as its
explicit external premises. Their proofs remain outside the user's current
work scope. P0 and WeightedCapture are still unproved: the general structural
model and descent stages remain separate tasks.

## Exact statement

For m>=D>=1 and rho,C>0, positive Q,E,N0 are fixed before N, a in R/Z and
the actual finite set S of nonzero integers in [-N,N]. For N>=N0, if
|S|>=rho*N and every original retained h satisfies

    ||h^D*a|| <= C/N^m,

then an actual positive integer q<=Q satisfies

    ||q*a|| <= E/N^(m+D).

The critical m=D case is included. The original N is retained in both
denominators. The proof actually permits zero in S as well, because the
uniform cardinality thresholds absorb a singleton; the exported proposition
keeps the original manuscript's nonzero-set condition.

## Uniform seed, with the center chosen afterwards

The integer bucket map h -> (h+N)/L has at most 2*N/L+1 values. Uniform
choices L=ceil(8*(D+1)/rho) and N0>4*(D+1)/rho force one actual bucket
to contain D+1 distinct original returns. A subset of exactly that size
is reindexed as H+v(i), with v an injective map into Fin L. This is an
explicit reindexing of retained original integers.

For a fixed relative integer pattern v, rational Lagrange interpolation
applied to (X+H)^D extracts its leading coefficient 1. The rational weights
depend only on v. A common nonzero integer denominator is chosen before H,
giving integer coefficients c_i and q with

    sum_i c_i*(H+v(i))^D = q   for every integer H.

There are finitely many maps Fin(D+1)->Fin L. Taking a finite sum bound on
their integer denominators and coefficient absolute values gives a positive
uniform Q before N, H, a or the return error epsilon. The circle triangle
inequality yields ||q*a||<=Q*epsilon, retaining |q| as a positive natural
multiplier. This finite-family argument is a general proof over every center
and every input, not a numerical test of selected patterns.

## Full power gain from actual same-sign rounding fibers

One sign contains at least half the original returns. A negative sign is
reflected by an injective map, with original provenance and the even/odd
power identity recorded. The resulting nonnegative set T has
|T|>=|S|/2 and the same circle return bounds.

Choose a nearest real representative u of q*a. The seed gives
|u|<=A/N^m, with A=Q*C. Since m>=D and N>=1,
|u|*N^D<=A. Thus the actual integers round(u*h^D) belong to
[-K,K], where K=ceil(A+1); write B=2*K+1.
Each return has real rounding error at most Q*C/N^m.

An actual rounding fiber contains at least |T|/B integers. Its maximum and
minimum differ by at least the fiber size minus one. For nonnegative x<=y,

    (y-x)^D <= y^D-x^D.

This algebraic inequality and the common rounding target imply

    |u|*(|T|/(2*B))^D <= 2*Q*C/N^m,

once the uniform threshold ensures |T|>=2*B. Because |T|>=rho*N/2,
one may take

    E = 2*Q*C / (rho/(4*B))^D.

This proves the required N^(-(m+D)) bound on the same q*a. It uses no
derivative estimate near zero, no division by a circle multiplier, no extra
equidistribution input, and no inference about responses at reflected points.

## Consequence and remaining scope

F31 had already proved the actual bounded-denominator adapter, current-row
top relation, no-relation compressed-block count and operator bound,
constructed lower-degree children with every rational/root branch, and
complete natural-degree induction. Substituting the new proved return lemma
now gives

    uniform_ordinary_freezing_of_weyl
      (hW0 : CubicTwoCoefficientWeylInput)
      (hW  : PolynomialLeadingWeylInput)
      (D : Nat) : UniformOrdinaryFreezing D.

Its constants precede N and every original horizontal coefficient field.
The same original input, complete response labels, arbitrary point assignment,
and the s/3, s/12, s/3 error budgets remain. No internal return, child-existence
or degree-termination premise remains in this ordinary theorem.

The general rational polynomial observation models still require precise
output types and realization, integer polynomial modules, nilmanifold
construction, forced relations, rational descents and uniform structural
termination. Ordinary freezing alone does not complete those stages or the
original-frequency capture and P0 targets. The twelve erroneous historical
three-dimensional applications remain deferred and unused; P2-CSE and U0
remain open.

The 13 new declarations are in MonomialInterpolation.lean, MonomialSeed.lean,
MonomialAmplification.lean and MonomialReturns.lean. The exact Lean proposition
remains in MonomialReturnInterface.lean. See verification/result.json for the
build and exhaustive transitive-axiom audit.
