# F34: constructed coordinate flag and proper observation difference space

Update at F35: this actual flag now proves nilpotence of the observation
group with class(H)<=class(G)+R*(D+1)^m+1 for a nilpotent base. Its full
commutator subgroup and the real-linear form of actual continuous characters
are proved. Full rational/Lie structures and bounded integer bases remain
open. See OBSERVATION_NILPOTENT_INTERFACE.md.

The complete P0 and WeightedCapture targets remain unproved. This checkpoint
proves the weighted-polynomial step used in the actual manuscript's Section 4,
starting with the sentence asserting that translation differences lower
weighted degree. It removes the abstract common-flag premise from the
constant-in-W argument under explicit triangular coordinate hypotheses.
It introduces no new external analytic input or project axiom.

## Actual polynomial lowering

For a weight function w on the coordinate indices, `weightedPolynomialBelow w n`
is the real submodule of multivariate polynomials whose every nonzero monomial
has weight strictly less than n. Its level zero is exactly the zero space.
These are actual support conditions, not upper bounds attached to arbitrary
syntactic expressions.

For substitution T(X_i)=X_i+q_i with q_i of weight strictly below w_i, the proof
first establishes multiplication and power bounds, then expands each actual
monomial and the actual support sum of an arbitrary polynomial. The result is

    P in level (n+1) implies T(P)-P in level n,
    P in level n implies T(P) in level n.

The conclusions include zero polynomials, constant polynomials and cancellation
of declared leading terms. There is no nonzero-leading-coefficient assumption.
No finite sample is used to prove these identities or their degree bounds.

## Coordinate hypotheses and constructed flag

Let V be the actual translation-invariant real function module on a group G.
Supply coordinates c_i:G -> R and actual coordinate polynomials q_(g,i) such that,
for every translating element g and every u in G,

    c_i(g*u) = c_i(u) + q_(g,i)(c(u)).

For given positive coordinate weights, assume q_(g,i) has strictly smaller
weight than w_i. Evaluation is a genuine linear map from polynomials to
functions on G, and the exact coordinate identity intertwines T_g with the
polynomial substitution. Define the flag by intersecting V with the image
of each weighted polynomial subspace. This constructs the increasing levels,
their zero bottom, and the strict lowering of all actual differences in V.
A polynomial representative always evaluates to the same observation function;
it is never used as an independently reselected field.

For a triangular presentation on m ordered coordinates, each q_(g,i) uses
only coordinate variables j<i and has ordinary total degree at most D,
uniformly for all g. The explicit prior weights

    w_i = (D+1)^i

satisfy all strict correction bounds. If every observation in V has an actual
polynomial representative of ordinary total degree at most R, the explicit
uniform flag height is

    K = R*(D+1)^m + 1.

Both depend only on m,D,R, with no size restrictions on any real coefficients.
The theorem includes D=0, zero corrections and lower actual degrees. The
coordinate formulas and degree/support conditions are explicit hypotheses;
this does not yet prove that every abstract Malcev presentation supplies them.

## Consequences for W and its integer intersection

The constructed flag and the F33 minimal-level argument imply that a
nonconstant V containing one has 1 in the actual difference space W.

Properness is also proved: choose the least flag level containing all of V.
Every translation difference, and hence their full real span, belongs to
the previous level. That level cannot contain all of V by minimality.
This proves W is proper without assuming an already chosen quotient basis
or declaring a nonzero top coefficient.

Finally, W intersect V_Z is implemented as an actual additive subgroup of
V_Z. It is proved saturated: if n is a nonzero natural number and n*P belongs
to W, then P belongs to W. This cancellation occurs in the real vector space;
there is no division of circle values or deletion of circle-root branches.
The theorem does not presume that V_Z has already been proved a full lattice.

## Exact obstruction to an ordinary-degree shortcut

The substitution X_1 -> X_1+X_0 has difference X_0. Both the original X_1
and its difference have ordinary total degree one, so strict lowering of
ordinary degree is false. With w_0=1 and w_1=2, the actual difference has
strictly smaller weight. This is machine-checked as a polynomial identity,
not a numerical test or a counterexample to P0.

## Next necessary core work

1. Encode the full rational Malcev coordinate presentation, and connect its
   actual group laws to the triangular coordinate conditions proved here.
   Retain uniform coordinate degree and rational-height bounds.
2. Prove W rational and V_Z a full lattice; construct the required bounded
   integer quotient and character bases. Saturation alone supplies no basis.
3. F35 completes the observation group's nilpotence under the coordinate
   hypotheses and its full commutator description. Complete the rational/Lie
   presentations and polynomial filtrations, and the mean-zero
   observation's quantitative boundary estimates.
4. Derive the general relation types and construct the rational descent
   branches with uniform termination. Connect actual structural extraction
   and realization to the original theta before using the terminal capture.

The new algebra changes no original response, retained measure, label set,
circle-root rule or target quantifier. It does not assert general structural
model existence, structural freezing, or P0. P2-CSE and U0 remain open, and
the twelve deferred three-dimensional applications remain unused.

## Verification

Run `python verify.py` for the whole project and exhaustive explicit-theorem
axiom audit. This checkpoint adds 33 theorem declarations; the expected total
is 1066. All new proof dependencies must remain within the same standard
Lean/Mathlib foundations as earlier checkpoints.
