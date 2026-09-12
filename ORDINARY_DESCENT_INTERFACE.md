# F31: actual ordinary children and conditional degree induction

Update at F32: MonomialDenseReturns is now proved. The following records the
F31 boundary; the current all-degree ordinary theorem has only the two
external Weyl premises. See MONOMIAL_RETURNS_INTERFACE.md. P0 remains open.

P0 and WeightedCapture are still unproved. This checkpoint constructs the
ordinary polynomial children and connects the complete degree induction.
The induction has TWO external analytic premises and ONE unproved internal
core premise. These roles must not be merged.

The external premises are CubicTwoCoefficientWeylInput (for the D=0 base)
and PolynomialLeadingWeylInput (for D>=2 single-block relations). The user's
current scope leaves their deep proofs outside this work phase. Their exact
statements and source adaptations remain explicit and unproved.

The internal premise is MonomialDenseReturns. It is the manuscript's dense
monomial return lemma, not an exempted external theorem, a project axiom,
or a theorem proved by the new conditional assembly.

## Actual child construction: proved without the three premises

OrdinaryTopRelation D Q E N a means that an actual positive integer q<=Q
satisfies

    ||q*a||_(R/Z) <= E/N^(2*D+3).

For every original y in [N^2], multiplication by the actual integer y^D
puts y^D*a in MajorArc(max(Q,ceil(E)),N). This keeps q as a positive
multiplier; there is no division on the circle. The factor y^D is at most
N^(2*D), producing exactly the N^(-3) scale.

For each Q>0, E>=0 and epsilon>0 there is a positive J before N and all
original data. For each N>0, real offsets c_i are fixed before D and every
coefficient field. For each top-coefficient field a(x), an actual point
assignment j(x,y) is then chosen, independently of the lower coefficients.

The children are actual real polynomials

    P_i(x) = erase_D(P(x)) + c_i.

For D>0 and degree(P(x))<=D, every child has degree at most D-1 at every
horizontal point. All nonconstant lower coefficients are exactly the original
ones. Zero polynomials and parents of actual degree smaller than D are included.
Each child formula is globally defined on the original box, not just on the
points assigned to it. On every original point whose top coefficient has the
displayed relation, the selected child has circle error at most
epsilon/(2*N^3). The parent and child use the same original input and all
original response labels.

The existing explicit major-arc grid retains all rational residues and circle
root branches. Selecting real representatives of these offsets makes them
actual polynomial constant terms; it does not eliminate any grid branch.
An exact obstruction for every D and N shows why branches are necessary:
the coefficient 1/2 has a vanishing double, but replacing (1/2)*y^D by zero
has circle error 1/2 at y=1. This refutes a descent shortcut, not P0.

## Exact remaining return statement

MonomialDenseReturns quantifies D,m with m>=D>=1 and rho,C>0. It supplies
positive Q,E,N0 before N, a in R/Z and the actual finite set S of nonzero
integers in [-N,N]. If |S|>=rho*N and every h in S satisfies

    ||h^D*a|| <= C/N^m,

then some positive q<=Q satisfies ||q*a||<=E/N^(m+D). The critical m=D
case is included in the statement but is not proved. The D=1 instance is
proved separately from the existing affine return theorem.

The bounded-multiplier adapter is proved conditional on this exact premise.
It selects an actual denominator fiber, pays density rho/B, retains nonzero
displacements, and multiplies positive denominators instead of cancelling them.

## Conditional block count and induction

From F30's actual current-row block relation, many large original compressed
blocks give a set of distinct nonzero horizontal displacements. Their exact
cardinality is retained. The return premise is applied at m=D+3, giving the
top relation at N^(-(2*D+3)). Its contrapositive gives a genuine no-relation
block count. Original masks vanishing on relation rows have small energy by
the checked block Schur estimate, including the separate diagonal 1/N.
These higher-degree conclusions remain conditional on MonomialDenseReturns.

Given target 0<s<=1, the proof first fixes no-relation constants for s/3.
It constructs the child list with epsilon=s/(12*pi), fixes its size J, and
only then applies the lower-degree statement at s/(3*sqrt(J)). The final
cutoff is twice the child cutoff, and the threshold is the maximum of the
required thresholds. All are fixed before N and the original coefficients.
The same-input error and disjoint assignment estimates retain the budgets
s/3, s/12 and s/3. Strong induction on the natural degree terminates without
any presumed list of children or unproved termination premise.

The final checked implication is

    CubicTwoCoefficientWeylInput -> PolynomialLeadingWeylInput ->
    MonomialDenseReturns -> forall D, UniformOrdinaryFreezing D.

It does not remove the internal return obligation. Ordinary freezing alone
would still not supply the general structural model types, their realization,
rational descents, uniform structural termination, or the complete capture
and P0 theorem. The twelve historical erroneous three-dimensional applications
remain deferred and unused. P2-CSE and U0 remain open.

The 19 new theorem declarations are in OrdinaryChildren.lean,
MonomialReturnInterface.lean, OrdinaryTopRelation.lean and OrdinaryFreezing.lean.
See verification/result.json for the actual build and exhaustive axiom audit,
and MONOMIAL_RETURNS_PROOF_PLAN.md for the next core proof target.
