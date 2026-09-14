# P0 formalization

Status: in progress; the complete P0 theorem has NOT been formally verified.

Checkpoint F37: 1161 checked theorem declarations. A supplied actual finite
real basis represented by rational coordinate polynomials, together with
the actual subgroup coordinate image being the full integer grid, now proves
that the original integer-valued subgroup is discrete and spans V over R.
Exact integer evaluations also construct a finite integer basis. Its height
and adaptation to W, the full rational presentation, group lattice
cocompactness, boundary estimates and general structural descents remain
open. See OBSERVATION_INTEGER_LATTICE_INTERFACE.md for the exact scope.
The earlier checkpoint paragraphs below retain their historical scope.

At F36, 1142 theorem declarations were checked. Actual bounded-degree
polynomial representatives now prove finite-dimensionality, the pointwise
module topology and closed W. With continuous coordinates, evaluation and
translation are jointly continuous and H is an actual topological group.
A literal rational polynomial translation matrix and surjective coordinates
give a finite rational-coordinate generating list for W. Constructing the
full rational presentation, full lattices and bounded integer bases, boundary
estimates and general structural descents remain open. See
OBSERVATION_RATIONAL_INTERFACE.md for the exact inputs and conclusions.

At F35, the actual commutator
subgroup is proved to be [G,G] times the real difference space W, with
every real multiple justified by actual commutators. The constructed
triangular flag gives class(H)<=class(G)+R*(D+1)^m+1 for a nilpotent base.
Actual continuous characters now have real-linear fiber restrictions
annihilating W, with exact source-term cancellation and lattice integrality.
Rational presentations and full lattices, bounded integer bases, observation
analysis and general structural descents remain open. See
OBSERVATION_NILPOTENT_INTERFACE.md for the hypotheses and remaining work.

At F34, actual triangular
coordinate formulas now construct a common lowering flag, with explicit
weights and height depending only on fixed degree and dimension bounds.
This proves 1 in the observation difference space W and W proper for a
nonconstant module, without a supplied abstract flag. The integer intersection
is also proved saturated. General rational Malcev structure and structural
freezing remain open. See COORDINATE_FLAG_INTERFACE.md.

At F33 the observation group,
its actual integer-valued subgroup, fixed coset observation and exact original
block-phase encoding are now checked. The common-flag implication for 1 in W
and an exact missing-pullback obstruction are also checked. General rational
structure, boundary estimates and structural descents remain open. F34 and
F35 supply the coordinate flags and nilpotence under their exact hypotheses.
See OBSERVATION_GROUP_INTERFACE.md for the exact scope and next obligations.

Earlier core results: Actual paired-shift
representation counts, exceptional-pair deletion and uniform density energy
are now proved. These combine with the checked local-to-global comparison
and complete frequency mesh to give positive original weighted real seven-cubes
conditional on `CyclicConcatenationInput`. The uniform theorem preserves one
fixed real lift, original safe-window mass and complete original responses.
All constants precede the scale and original data.

F22 adds complete seven-vertex collision deletion, high-weight thresholding,
the exact unweighted q^8 normalization and uniform horizontal fibre selection.
Supplied structural subsets can then be transported back to actual original
base points, preserving a uniform original-mass lower bound, circle error to
d*theta and full original responses. These transport theorems do not assert
that a structural model exists or label an arbitrary matching function a
nilpolynomial. See STRUCTURAL_VALUE_INTERFACE.md.

F23 adds 39 checked results for finite Schur estimates and arbitrary pointwise
output masks. Every original horizontal Gram block has norm at most 1/N.
For a mask supported on retained horizontal rows, if each such row has at
most rho*N actual large compressed blocks and the other retained off-diagonal
blocks have norm at most v/N, the masked original operator has norm at most
sqrt(rho+v+1/N). This gives the original minor-arc estimate conditional
on that block count, with error parameters fixed before N and the original
data. The exact K=1/2 obstruction rules out dropping the square root.
The count itself remains unproved for the structural profiles.
See FINITE_BLOCK_SCHUR_INTERFACE.md.

F24 adds 31 checked results for supported circle-error operator stability,
exact arbitrary child assignment, different child minor-arc cutoffs and the
three-piece freezing assembly. The bounds s/3, s/12, s/3 fit inside s. A
uniform wrapper chooses numerical parameters before N and all data, and
deduces the parent finite estimate from actual compressed-block counts and
supplied approximating children with their individual estimates. It does
not construct structural children or prove termination. Exact counterexamples
check the assignment loss and the need for major-arc closeness.
See FREEZING_STEP_INTERFACE.md.

F25 adds 42 checked results for a finite vertical enlargement, exact recovery
of every original horizontal block, complete four-factor Gram phases and the
N^(-4) large-block estimate. Failure of an actual compressed v/N block bound,
at N*v^2>=2, yields at least N*v^2/4 nonzero lags with complete phase sums
at least N*v^2/8, each at its own original source root. A uniform wrapper fixes
c and N0 before all profiles and masks. An exact two-term counterexample checks
the invalid comparison between truncated and complete phase sums. No external
deep input is used by these new results. See WIDE_BLOCK_INTERFACE.md.

F26 adds 25 checked results for actual affine vertical profiles. Their complete
cubic phases, shorter-interval Weyl estimates with the original N denominator,
two actual block directions and bounded-multiplier returns give the N^(-5)
top-slope relation on rows with many large compressed blocks. The contrapositive
proves the no-relation block count, and the original operator on those rows has
norm at most any prescribed s after a uniform threshold. Arbitrary pointwise
contractive masks and the same original input remain. An exact quarter-slope
obstruction checks the retained factor 8. This uses the proved cubic Weyl theorem,
not a new external input. See AFFINE_FREEZING_INTERFACE.md.

F27 adds nine checked results constructing the actual affine relation-row
children. Their number precedes N and all original coefficients; the explicit
grid offsets precede the slope and intercept fields, and all rational branches
are retained. These children are constant in the vertical variable and retain
the original horizontal intercept dependence. With these constructed children
and F26's no-relation estimate, complete affine freezing is reduced to the
explicitly unproved degree-zero core proposition UniformConstantFreezing.
It is a theorem premise, not a new axiom or an established external input.
See AFFINE_CHILD_INTERFACE.md and CONSTANT_FREEZING_PROOF_PLAN.md.

F28 adds 23 checked results for the degree-zero Fourier passage: the exact
positive translation multiplier, fiberwise counting-energy transfer, injective
cyclic input zero extension, and complete original endpoint/response recovery.
The cubic and quadratic phases are both retained, and the cyclic normalization
cancels with no loss. Restriction to the original output follows the full
cyclic estimate. The exact reduction to UniformHorizontalConstantFreezing
preserves Q,N0; this horizontal core proposition is still unproved. Its Gram
kernel, simultaneous coefficient estimates and actual large-entry count remain.
See CONSTANT_FOURIER_INTERFACE.md.

F29 adds 31 checked results for the genuine horizontal Gram kernel, complete
I_h labels, all four phase coefficients, the actual large-entry count and
scalar Schur estimate. The final degree-zero and complete affine freezing
theorems assume only CubicTwoCoefficientWeylInput; all internal estimates and
children are supplied by checked proofs. This explicit external analytic
input is neither a new axiom nor a proved theorem. Its conversion from an
external library statement remains outside the checked chain. All cutoffs
precede N and the original coefficients. See CONSTANT_FREEZING_INTERFACE.md.

F30 adds 26 checked results for genuine ordinary polynomial profiles and
their exact original responses. For every D>=2, the actual double-phase
polynomial has degree at most D+2 and top coefficient
-3*k*(2*h)^D*a_D(x+h), with the zero/lower-degree cases included. An exact
D=1 obstruction preserves the affine exception. From the explicit
PolynomialLeadingWeylInput, each actual compressed large block forces a
bounded positive multiple of h^D*a_D(current row) at N^(-(D+3)), with constants
before N, all original coefficients and masks, and without synchronizing roots.
The nonlinear return in h, actual lower-degree children and induction remain
open. See ORDINARY_BLOCK_INTERFACE.md.

F31 adds 19 checked results constructing actual lower-degree polynomial
children, retaining original lower coefficients and every circle branch.
Their positive count and offsets precede N-dependent original coefficient
fields; the point assignment depends only on the top field. The actual block
count, no-relation operator and complete degree induction are now connected
CONDITIONALLY on the two explicit external Weyl inputs AND the still-unproved
INTERNAL core premise MonomialDenseReturns. That premise is not an external
deep-theorem exemption or a project axiom. An exact half-frequency obstruction
prevents zero-branch deletion. See ORDINARY_DESCENT_INTERFACE.md and
MONOMIAL_RETURNS_PROOF_PLAN.md. P0 remains unproved.

F32 adds 13 checked results proving MonomialDenseReturns without any
unproved premise, including the critical m=D case. Actual bounded clusters,
integer interpolation uniform in the center, and same-sign rounding fibers
give the full N^(-(m+D)) return scale. Substitution in the F31 induction
now completes ordinary polynomial freezing in every fixed degree from only
the two explicit external Weyl inputs. The general structural model and
descent stages remain open. See MONOMIAL_RETURNS_INTERFACE.md.

F33 adds 35 checked results around the actual right semidirect observation
group. Integer-valued translations and all right lattice corrections give
a well-defined unit-modulus observation on the coset quotient. Its curve
agrees exactly with the complete original block phase and lag sum. A supplied
common lowering flag for a nonconstant module implies 1 in W, allowing the
source polynomial to vanish in the constructed horizontal character. No
rationality, nilpotence, full lattice property or flag existence is inferred
from the algebraic types alone. An affine example proves that omitting the
pullback can change the phase by exactly half a circle. P0 remains unproved.

F34 adds 33 checked results for actual weighted polynomial support spaces,
strict lowering under triangular substitution, exact coordinate evaluation,
constructed common flags, proper W and the saturated integer intersection.
The weights (D+1)^i and height R*(D+1)^m+1 are fixed before all coefficients
and translations. An exact polynomial example shows why ordinary total degree
cannot replace weighted degree. The full rational Malcev presentation still
needs to supply the explicit coordinate hypotheses, and rationality, full
lattices, observation analysis and general descents remain unproved.

F35 adds 43 checked results for actual commutator generation, lower-central
flag descent, continuous real-linear character restrictions and their
integer and nontrivial components. The same original curve loses its source
term in every such character. The topology is the actual product with the
pointwise observation subspace; a full Lie/Malcev comparison is not inferred.
An exact affine example shows that an abelian base need not give abelian H.

F36 adds 33 checked results connecting the bounded-degree function module
to finite-dimensional topology and actual joint continuity. A general
value-span/coefficient-span identity proves rational W from the actual
rational polynomial translation matrix, with an explicit finite list and
cardinality bound. The exact restricted-parameter example explains why the
coordinate-coverage premise must be retained. Full rational presentation and
lattice construction remain necessary. See OBSERVATION_RATIONAL_INTERFACE.md.

Following the user's 2026-09-12 instruction, current work prioritizes the
manuscript's own core arguments. External deep theorems are explicit inputs;
their proofs are outside this work phase. They are neither new Lean axioms nor
counted as proved. Nonlinear monomial returns and the ordinary internal
freezing chain are complete. Structural value extraction, general structural
block counts, rational descents and uniform structural freezing are still open.
See CORE_SEVEN_CUBE_CHECKPOINT.md for the exact new scope.

The earlier checked spine remains: The recursive box moment now
equals the full Boolean-vertex expansion in C, with all multiplicities intact.
The complete cyclic rerooting and t-average reindexing are checked. Sixteen
original weights remain outside the cubic t sum, whose leading coefficient is
minus the signed original frequency sum and is independent of the lag k.
The resulting weighted norm average is >=(a/4)^16 with uniform constants and
original responses retained. Every nonzero-weight cube vertex is an actual
retained original base point. Linear inverse Weyl estimates are now proved for
all affine phases and actual integer intervals with the original N denominator.
Exact differencing, explicit nonzero-shift counts above N*rho^2>=2, a checked
small-scale obstruction, and quadratic/cubic phase derivatives are established.
Dense affine recurrence amplification and the quadratic/cubic leading-coefficient
inverse estimates are now checked, at every positive scale. One common denominator
is chosen before the scale and all coefficients. Applied to the actual original
cube time sum, it retains weighted cube mass >=(a/4)^16/2 at scale N^(-3), with
the same original safe mass and complete responses. This captures a cube coefficient,
not an original point frequency. The unused k mean is now removed exactly;
simultaneous sign reflection fixes every actual vertex and gives the positive-h
mean with no loss. Pair collisions cost at most 1/(2*ell+1), and the complete
120-pair union costs at most 120/(2*ell+1). A uniform data-independent threshold
leaves distinct-vertex original weighted cube mass >=(a/4)^16/4, preserving the
same original safe mass and complete responses. The nonzero modular step and
short interval hypotheses are explicit; a checked zero-step counterexample
shows why the former cannot be omitted. One simultaneous real lift is now
checked: every point receives one of 57 choices shared across all cubes.
The same rounded values give S=l*M_lift+r, |l|<=8 and |r|<=9. Uniform restriction
to distinct vertices and weighted expectation retain real-zero four-cube mass
>=(a/4)^16/(4*57^16). Here M_lift=floor(N^3/E)>=9, |F|<=3, F lies on the grid,
and its supported circle error to d*theta is <=19*E/N^3. Constants precede N,q
and all original data, and original responses remain unchanged. Exact frequency
averaging is now checked on the complete j/1024 mesh for all dimensions <=7,
with grid integrality and the strict size bound. It detects real zero and
retains every original weight. The same F has local fourth-norm sixteenth
moment >=beta=(a/4)^16/(4*57^16), and at least beta/2 of actual (x,j) fibres
have mean_h local norm >=beta/2. All multiset multiplicities and complete
original responses remain in the uniform theorem. The local-to-global comparison
is checked. F21 closes the core passage to real seven-cubes relative to the
explicit external concatenation input. Structural realization, uniform freezing
and the remaining operator bounds are open.

Primary source: ../GMZ_P0_Zenodo/sections/01-introduction.tex through 05-selection.tex.
Original contract: ../GMZ_P0_Phase40_Final_Adjudication/historical_contracts/phase12_capture_contract.json.

The main target preserves the order `delta, c(delta), N, f, theta` and uses the
same original function in the conclusion. The stronger weighted target preserves
the original weight, all cubic labels, all circle roots, and uniform list size.

Lean 4.33.0 and Mathlib v4.33.0 are pinned. Official dependency source archives
use the precise revisions in Mathlib's original manifest, recorded in
dependency-provenance.json. Local path dependencies avoid an unreliable Git
transport in this environment; no upstream mathematical source has been edited.

In the configured workspace, run `python verify.py` to build and audit all
theorems. With Lean 4.33.0 and Python installed, `./setup.ps1` retrieves the
official sources and builds from source on a fresh Windows checkout.
Optional `./setup.ps1 -UseCache` retrieves official compiled artifacts first.
The setup script accepts `-Python` for an explicit Python executable path.
The regular build command is `lake build`; the axiom audit is
`lake env lean GMZP0/Audit.lean`.

See STATUS.md for the exact current checked scope and remaining obligations.
Proved declarations must have no `sorry` or added axioms.
Unproved results are recorded as propositions or in the dependency ledger;
conditional reductions must explicitly name their hypotheses.

No historical claim of proof, successful numerical test, hash, or document
compilation counts as a formal proof. U0 is outside this target. The twelve
deferred erroneous three-dimensional applications must remain unused.
