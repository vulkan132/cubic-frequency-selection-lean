# F36: finite-dimensional topology and rational coefficient generation

Later update: F37 proves discreteness, full real span and a qualitative
integer basis of V_Z from an actual rational polynomial basis and exact
integer-grid presentation of Gamma. See OBSERVATION_INTEGER_LATTICE_INTERFACE.md.
This F36 document retains its checkpoint-specific scope below.

P0 and WeightedCapture remain unproved. F36 proves additional internal
steps in the manuscript's observation-module construction. No new external
premise or project axiom is introduced. The source is the actual Section 4,
`../GMZ_P0_Arxiv_Paper/sections/04-freezing.tex`, particularly the integer
polynomial module, rationality of W, and semidirect-group paragraphs.

## Finite-dimensionality from actual representatives

Let coord:G -> (sigma -> R), with sigma finite. Suppose that for every
actual F in V there is a polynomial P of ordinary total degree at most R
whose evaluation equals F at every point of G. Then

    V <= image(evaluation, polynomials of total degree <= R).

The polynomial space is finite-dimensional. Its image, and then the actual
subspace V, are finite-dimensional. `observation_finrank_le_polynomial`
bounds dim(V) by the dimension of this fixed polynomial space. The
polynomial-space bound depends only on sigma and R, before coefficients or
translations; a closed-form binomial dimension count is not claimed here.
No injectivity or surjectivity of coord is needed for this conclusion.

The pointwise subspace topology used in F35 is proved to be the real module
topology on this finite-dimensional Hausdorff space. The map to coordinates
of any finite real basis is continuous. Each fixed linear translation is
continuous, and the actual W is closed. W has not been enlarged by closure.

## Joint continuity of the real observation group

For a finite-dimensional space V of continuous real functions on G,
evaluation (P,u) -> P(u) is jointly continuous. The proof expands P in an
actual finite basis, whose coefficients are continuous in the pointwise
topology; it then uses a finite sum of products of continuous functions.

If G is a topological group, this proves joint continuity of the actual
pullback (g,P) -> T_g P. The previously constructed group operations

    (g,P)*(h,Q) = (g*h,T_h P+Q),
    (g,P)^(-1) = (g^(-1),-T_(g^(-1)) P)

are therefore continuous in the existing product topology.
`observation_topologicalGroup_of_degree` obtains the function-continuity
and finite-dimension hypotheses from one continuous coordinate map and
the same bounded-degree representatives. This proves an actual
`IsTopologicalGroup` instance proposition for H. A Lie structure,
smoothness, lattice discreteness and cocompactness are not inferred.

## Values and coefficient vectors have the same real span

For a finite set S of exponent vectors and arbitrary vectors v_d in a
real vector space, define

    F(x) = sum_(d in S) x^d * v_d.

`vectorPolynomial_span_values` proves that the real span of all F(x),
for all real coordinate vectors x, equals the span of the coefficient
vectors v_d. The space of the v_d need not be finite-dimensional.

For the nontrivial inclusion, a linear functional separating a coefficient
from the value span would yield a nonzero scalar polynomial vanishing at
every real parameter vector. The proved multivariate polynomial identity
theorem forces every coefficient to vanish, a contradiction. This is a
general algebraic proof, not a sample evaluation or numerical rank check.

## Actual rational matrix presentation gives rational W

Supply an actual finite real basis b of V, a SURJECTIVE coordinate map
coord:G -> R^sigma, and a matrix A_(i,j) of genuine multivariate polynomials
with rational coefficients, satisfying the exact identity

    b.repr(T_g(b_j)-b_j)_i = aeval(coord(g), A_(i,j))

for every g,i,j. These hypotheses describe the actual translation
representation; they do not assume W or its rationality.

`rationalMatrixSupport` constructs the finite union S of the monomial
supports of every matrix entry. Actual polynomial evaluation, finite-sum
reordering and basis reconstruction give the vector expansion. For each
j,d the coefficient vector is

    v_(j,d) = sum_i (coefficient_d A_(i,j)) * b_i.

It has the specified rational basis coordinates, as separately proved.
Surjectivity of coord allows the value-span theorem to show that every
coefficient vector is in W. Conversely, exact real linearity and basis
expansion place every original T_g P-P in their span. Consequently

    W = span_R {v_(j,d) : j in basis indices, d in S}.

`observation_difference_rational_of_matrix` concludes `RationalInBasis b W`:
W is generated over the reals by a finite list of vectors with rational
coordinates in b. The constructed rational-coordinate list has at most
card(b-index)*card(S) entries, chosen from the fixed matrix before g or P.
This is rationality relative to the supplied basis. It does not yet
construct a rational basis of polynomial functions from full Malcev data,
nor the rational matrix A or a uniform height bound for it.

The current surjectivity hypothesis matches global Malcev coordinates.
The exact obstruction `polynomial_restricted_parameter_obstruction` shows
that X vanishes on the restricted coordinate image {0} while its linear
coefficient is 1. Hence arbitrary restricted values do not determine the
coefficient span. This is compatible with finite determining grids when
their sufficient degree and coverage conditions are proved; it is not a
counterexample to P0.

## Remaining core dependencies

1. Construct a complete rational Malcev coordinate presentation and the
   actual rational polynomial basis of V. Derive its translation matrices,
   surjective continuous coordinates, degree and rational-height bounds.
   F34-F36 now supply the consequences of those exact presentations.
2. Prove that the actual integer-valued subgroup V_Z is a full lattice.
   This requires the polynomial integer-value/basis argument and its
   restriction to the actual rational space. Use the proved saturation
   of W cap V_Z to construct adapted integer quotient and character bases,
   including the bounds needed for uniformly finite choices.
3. Complete the Lie/rational polynomial structure and observation-curve
   filtrations. Prove the fixed fiber mean-zero and boundary/Lipschitz
   estimates, then connect the precisely stated external quantitative
   equidistribution input.
4. Derive the two structural relation types from actual large blocks,
   construct all rational descent branches with retained individual
   degrees, and prove uniform termination and error budgets. Complete
   structural extraction/realization on original positive weight before
   applying the checked terminal capture and WeightedCapture -> P0.

All original-response, original-weight, full-label metric and circle-root
requirements remain in force. No circle division occurs in these real
vector-space arguments. The twelve deferred three-dimensional composite
applications remain unused; P2-CSE and U0 remain open. The user's exclusion
of external deep proofs does not exempt these remaining internal steps.

## Verification

F36 adds 33 theorem declarations in six modules:

- ObservationFiniteDimension: 8.
- PolynomialValueSpan: 3.
- ObservationRationalSpan: 7.
- ObservationTopology: 9.
- ObservationPolynomialMatrix: 5.
- PolynomialParameterObstruction: 1.

The project total is 1142. `python verify.py` builds the entire project and
checks the transitive axioms of every explicit project theorem, allowing
only propext, Classical.choice and Quot.sound. See the actual result in
`verification/result.json`. The theorem count describes audit coverage,
not a completion percentage for P0.
