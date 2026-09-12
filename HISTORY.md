# Formalization checkpoints

These labels are separate from the manuscript research phases.

- F01 (2026-09-06): 22 checked declarations; original definitions, five phase
  identities, full-response comparison, conditional finite selection and the
  scale-dependent small-scale bound. No full WeightedCapture -> P0 reduction yet.
- F02 (2026-09-06): 49 checked declarations; adds the fully quantified conditional
  reduction, triangle inequality, N^(-3) circle scale, all integer root branches,
  exact zero-branch counterexample and real grid rounding. Both main target
  propositions remain unproved. See STATUS.md for remaining dependencies.
- F03 (2026-09-06): 67 checked declarations; adds the universal major-arc list,
  original-weight energy and mass estimates, the exact finite input geometry,
  and the complete conditional terminal passage from model approximation and
  finite operator estimates to capture. Uniform model existence and the relevant
  operator estimates have not been proved.
- F04 (2026-09-06): 104 checked declarations; adds exact endpoint collision
  geometry, the linear-first finite adjoint identity, original-label Gram
  expansion, the I/N same-horizontal block, original-weight adjoint energy
  and the h=0 split. Restriction and scaling keep the exact original mass and
  response. Grouping complete horizontal fibers gives the first TT* bound.
  The second signed statistic, k=0 estimate and safe-window justification
  remain unproved. The two main target propositions are still unproved.
- F05 (2026-09-06): 138 checked declarations; adds the second adjoint with an
  explicit horizontal window X, nonparallel collision uniqueness, exact kernel
  size and the N^(-3) row energy bound. The second finite Gram diagonal is
  nonnegative and costs at most mu(D)/N after normalization. The finite signed
  lower bound preserves both original weights and alignment phases. Safe-window
  shift geometry is checked, but construction of a uniformly positive-mass
  window and identification with the paper's lag-indexed statistic remain open.
  An exact counterexample records why a zero pairing does not imply zero adjoint
  energy; the checked second statistics keep X explicitly. P0 remains unproved.
- F06 (2026-09-06): 165 checked declarations; adds uniform positive-mass safe
  windows, exact strip mass accounting and interval partitions. M=ceil(64/kappa)
  and c=kappa/(4M) precede N and the data. The original finite signed statistic
  is uniformly positive for admissible data at N>=ceil(128/(eta^4*c^4))+1,
  with zeta=eta^4*c^4/256 and S_fin>=2*zeta. Original pointwise response on the
  nonzero weight support is retained. Lag-index equality and the downstream
  structural extraction/freezing proof are still open; P0 remains unproved.
- F07 (2026-09-07): 223 checked declarations; adds exact single-block and full
  two-label Gram formulas, canonical original lag sources, circle-valued phase
  identities and complete integer-label reindexing. Equal labels correspond
  precisely to k=0. The full finite statistic equals the explicitly finite
  lag statistic at scale N^(-6), with original fields and both weights intact.
  Uniform positivity transfers through that equality. Rerooted averaging,
  smoothing, local cube extraction and uniform freezing remain unproved.
  P0 and WeightedCapture remain unproved; no new mathematical axioms are used.
- F08 (2026-09-07): 257 checked declarations; adds the complete t=r+k-h sum
  bijection and exact rerooted interval, the actual nonnegative k=0 contribution
  and its original-mass upper bound mu(D)/N. The exact g(k)e(P(k)) separation,
  N-normalized B, N^(-5) outer sum, bounds |g|,|B|<=1 and weighted passage to
  moduli are checked. A uniform positive average over all original finite
  x,x',y,t indices retains the original response and mass. Conversion to Z/pZ,
  the factor 2p/N^2, smoothing and the downstream proof remain open. P0 and
  WeightedCapture remain unproved.
- F09 (2026-09-07): 288 checked declarations; adds the exact cyclic embedding,
  supported no-wraparound field/B identities and whole weighted vertical sums.
  Horizontal reindexing keeps all 2N nonzero shifts. The original finite
  modulus average equals (2q/N^2) times the cyclic average; the latter is a
  uniform average on 2qN^3 points, with weights in [0,1]. Its lower bound
  zeta/128 is uniform before N, q and all original data. A prime in the strict
  range 64N^2<q<128N^2 follows from checked Mathlib Bertrand. Smoothing, four
  box differences, structural extraction and freezing remain open; P0 is unproved.
- F10 (2026-09-07): 319 checked declarations; adds signed interval translation
  errors including empty intervals, exact finite mean identities and weighted
  perturbation bounds. Four independent shifts use (2*ell+1)^4 points and cost
  at most 8*ell/N<=a/8. The actual smoothed cyclic mean is >=7a/8 with constants
  before N, q and all original data, retaining original mass and response.
  Four explicit unit circle-phase factors are independent of their respective
  coordinates and reproduce the whole smoothed lag expression. No real lift
  or branch deletion is used. Box Cauchy–Schwarz, Jensen, Weyl extraction and
  the structural/freezing proof remain open. P0 and WeightedCapture are unproved.
- F11 (2026-09-07): 373 checked declarations; adds exact finite mean identities,
  moment Jensen inequalities and iterative box Cauchy–Schwarz in every dimension.
  Coordinate duplication preserves unit face factors and independence. The
  nonnegative box norm has the exact 2^d moment identity and bounds the actual
  four-shift average. Weights are removed only after nonnegativity is established;
  full lag extension costs (2N+1)/N<=3. The outer space has 2qN^3(2N+1) points.
  Its recursive box moment average is >=(a/4)^16 with all constants preceding
  N, q and original data, while original safe mass and full response remain.
  Explicit sixteen-vertex expansion, Weyl, structural extraction and freezing
  are still open. P0 and WeightedCapture remain unproved.
- F12 (2026-09-07): 416 checked declarations; adds the full Boolean cube expansion
  as a complex equality in every dimension, with parity conjugation and all
  multiplicities. The whole cyclic average is rerooted by Y=y+2hk using an
  explicit translation inverse. All sixteen original weights and alternating
  alignments are factored, and the t-cubic coefficient is exactly minus the
  signed frequency cube sum, independent of k. A finite bijection separates
  the complete t average. Its original weighted norm mean is >=(a/4)^16 with
  constants before N,q and original data. Every nonzero-weight vertex is an
  actual retained original base point with the same full response. Quantitative
  Weyl, common denominator, lag removal, sign symmetry and later structural
  steps remain open. P0 and WeightedCapture remain unproved.

- F13 (2026-09-07): 446 checked declarations; adds the inverse chord estimate
  and linear inverse Weyl on complete sums and every actual integer interval,
  always with the original N normalization and arbitrary affine intercept.
  Exact finite differencing keeps h=0 separately and proves a quantitative
  nonzero-shift count for N*rho^2>=2. A formal N=1 counterexample rules out
  omitting a scale condition. Quadratic/cubic circle derivatives and their
  actual overlap intervals are checked. A large quadratic sum yields a dense
  family with ||2*h*a2||<=4/(rho^2*N). Two nearby actual affine returns produce
  a bounded nonzero small multiple. Dense recurrence amplification and the
  quadratic/cubic inverse Weyl estimates remain open. P0 and WeightedCapture
  remain unproved; no external theorem was inserted as an axiom.

- F14 (2026-09-07): 473 checked declarations; proves quantitative affine
  recurrence amplification by actual bounded rounding fibers and integer
  diameter. Constants precede every input. Quadratic and cubic leading-coefficient
  inverse Weyl now hold at every positive scale, including small scales via
  the circle half-period bound. Actual interval rescaling and a dense fiber of
  actual positive denominators are checked. A factorial common denominator
  precedes N and all data. Applied to the exact original cube time polynomial,
  it preserves weighted cube mass >=(a/4)^16/2 at N^(-3), with all original
  safe mass and complete responses. The result controls the cube coefficient.
  Lag removal, sign symmetry, collision estimates, one global lift and later
  structural/freezing steps remain open. P0 and WeightedCapture remain unproved.

- F15 (2026-09-07): 516 checked declarations; adds exact removal of the unused
  k mean and simultaneous h/shift sign reflection fixing every actual vertex.
  Positive-h and signed means are equal with all sixteen weights intact.
  Coordinate resampling, short-interval injection and prime-field cancellation
  prove pair collision <=1/(2*ell+1); the complete 120-pair union is checked.
  An exact zero-modular-step counterexample shows that integer h!=0 is insufficient.
  One uniform threshold supplies all modular conditions and the collision budget.
  The resulting distinct-vertex weighted cube mass is >=(a/4)^16/4, with constants
  before N,q and every original input, retaining original safe mass and full
  responses. The full 2377-job build and transitive audit pass without warnings;
  only standard foundations occur. One global real lift and downstream structural
  and freezing proofs remain open. P0 and WeightedCapture remain unproved.

- F16 (2026-09-07): 565 checked declarations; adds one simultaneous real lift.
  A fixed [0,1) representative and actual nearest integer give S=l*M_lift+r
  with |l|<=8, |r|<=9, using the exact eight positive/eight negative signs.
  An allowed correction gives real fourth-difference zero. Restriction of one
  global point assignment to distinct vertices is uniform; success probability
  >=57^(-16) and weighted expectation give a single F shared by all cubes.
  M_lift=floor(N^3/E)>=9, F is on its grid, |F|<=3, zero original weight gives
  F=0, and supported circle error to d*theta is <=19*E/N^3. Real-zero cube mass
  is >=(a/4)^16/(4*57^16), with constants before N,q and original inputs, and
  all original safe mass and complete responses retained. An exact quantifier
  counterexample distinguishes separate witnesses from one shared choice.
  The full 2390-job build and 565-theorem transitive audit pass without warnings;
  only standard foundations occur. Exact frequency averaging, concatenation,
  structural realization and freezing remain open. P0 and WeightedCapture are
  still unproved.

- F17 (2026-09-07): 603 checked declarations; adds exact finite frequency
  averaging for grid-valued real cube sums in every dimension <=7. The full
  j/1024 mesh detects real zero using |k|<=384*M_lift<1024*M_lift. Integer
  frequencies and omission of the size bound have exact checked obstructions.
  Generic finite-multiset local moments are nonnegative, have the exact
  root-power identity, and yield norms in [0,1] for bounded functions. The
  actual cyclic local fourth-norm sixteenth moment equals the original
  weighted real-zero four-cube mass. One fixed F therefore has moment >=beta
  and a proportion >=beta/2 of actual (x,j) fibres with mean_h norm >=beta/2.
  All constants precede N,q and original data; the original safe mass and
  complete responses remain. The full 2401-job build and 603-theorem
  transitive audit pass without warnings; only standard foundations occur.
  Local-to-global comparison, family concatenation and deeper structural and
  freezing proofs remain open. P0 and WeightedCapture remain unproved.

- F18 (2026-09-07): 648 checked declarations. Adds finite abelian character
  inversion and Parseval, exact original parameter and difference densities,
  all-dimensional product pushforwards, local cube rerooting, and the exact
  positive Fourier expansion of local moments. Density energy is bounded by
  representation multiplicity with the uniform-measure normalization retained.
  The local comparison theorem explicitly retains the unproved character-twist
  estimate as a premise. Bounded-face box CS, finite permutation energy and an
  exact raw-probability normalization obstruction are checked. The full
  3064-job build and transitive audit pass; only standard foundations occur.
  The complete comparison, family theorem, structural and freezing proofs
  remain open. P0 and WeightedCapture remain unproved.

- F19 (2026-09-07): 677 checked declarations. Adds exact cross-correlation
  Fourier transforms, modulation, derivative energy and cube recurrence.
  A Fourier argument in dimension two and induction prove the character-twist
  bound in every dimension s>=2. An exact nontrivial character on ZMod 2 shows
  dimension one fails. The full multiset local-to-global moment and norm
  comparison is now proved without the F18 residual twist premise; an explicit
  positive local-norm to global-moment estimate is included. Complete mesh
  averaging gives exact weighted real-zero global cube mass for 1<=s<=7,
  including the actual cyclic seventh moment with the same F and original
  weights. The 3070-job build and 677-theorem transitive audit pass without
  warnings; only standard foundations occur. No positive seventh-moment lower
  bound is asserted without the still-open family theorem and pair geometry.
  Structural extraction, freezing, WeightedCapture and P0 remain unproved.

- F20 (2026-09-07): 688 checked declarations. Adds audited elementary
  paired-shift geometry. The actual local-fourth-moment bound yields a<=256;
  the result gives a uniform shrinking threshold, short shrunk radius, integer
  pair-shift range and no-wrap under the original prime scale. It also records
  bounded-event selection and the pair-shift seventh-norm upper bound. The
  full 3072-job build and transitive audit pass without warnings; only standard
  foundations occur. Gcd representation multiplicity, exceptional-pair
  counting, family concatenation, structural extraction, freezing,
  WeightedCapture and P0 remain unproved.

- F21 (2026-09-12): 712 checked declarations. Adds 24 core results: integer
  and cyclic paired-shift multiplicity <=1+2*A^2; exact multiple counts and
  finite reciprocal-square telescoping; exceptional-pair proportion <=3/A
  and <=u/4 at A=ceil(12/u); actual uniform density energy; selection of a
  good pair and its global seventh moment; propagation over actual good
  fibres and complete frequency averaging. The original-data theorem gives
  positive original weighted real seven-cubes conditional on the explicit
  uniform CyclicConcatenationInput. One F, original weights and full responses
  remain, and constants precede N,q and all original data. Following the user's
  instruction, external deep proofs are outside this work phase and are not
  counted as proved or added as axioms. The full build and transitive audit
  pass; only standard foundations occur. Structural value extraction,
  freezing, remaining operator estimates, WeightedCapture and P0 remain open.

- F22 (2026-09-12): 740 checked declarations. Adds 28 core results: arbitrary
  additive cube coordinate updates and pair collision bounds; all 8128 unordered
  seven-vertex collisions; a threshold loss <=tau; exact unweighted cube count
  normalization q^8; uniform collision thresholds and at least chi*N/4 good
  horizontal fibres, each containing at least (chi/4)*q^8 distinct high-weight
  real-zero seven-cubes. The original-data wrapper retains the same F, original
  weights, supported circle error and full responses, conditional only on the
  existing concatenation input at this stage. Separate transport theorems for
  supplied cyclic subsets prove original-box membership, exact preimage counts,
  mass >=64*rho*cModel*tau, error to d*theta and unchanged original responses.
  They do not assert structural existence or a nilpolynomial property for an
  arbitrary matching function. The complete build and axiom audit pass with
  only standard foundations. Structural types/input matching, realization,
  remaining operators, freezing, WeightedCapture and P0 remain open.

- F23 (2026-09-12): 779 checked declarations. Adds 39 core results: scalar
  row/column and symmetric block Schur estimates, exact adjoint energy transfer,
  complete horizontal regrouping and arbitrary pointwise contractive masks.
  All original horizontal blocks have norm <=1/N. At most rho*N actual large
  compressed blocks per retained horizontal row, with other blocks <=v/N,
  gives original squared energy <=(rho+v+1/N)*input energy. The actual minor
  mask yields FiniteMinorEstimate conditional on that count. Positive rho,v
  and N0 precede N,Q,p for every s>0. A one-dimensional exact counterexample
  verifies that the square root cannot be omitted. The full 3087-job build
  and transitive audit pass for all 779 declarations, using only standard
  foundations. No external deep input is used by these new proofs. The
  structural block count, phase-based large-block estimate, realization and
  uniform freezing remain open; neither WeightedCapture nor P0 is proved.

- F24 (2026-09-12): 810 checked declarations. Adds 31 core results: original
  operator contraction and positive averaging, supported full-label and circle
  error stability, exact disjoint pointwise child assignment, differing child
  cutoffs, nearby major-arc witness transfer and its usable contrapositive,
  the finite energy triangle and the s/3,s/12,s/3 assembly. A uniform one-step
  wrapper chooses numerical parameters before N,J,Q,all profiles and original
  point assignments; actual compressed-block counts and supplied approximating
  children with their finite estimates imply the parent FiniteMinorEstimate.
  Exact counterexamples check the J energy loss and the necessity of circle
  closeness for major-arc transfer. The manuscript's 0<s<=1 condition and
  a0=s/(12*pi) scale are retained. The full 3092-job build and 810-theorem
  transitive audit pass with only standard foundations. Structural production,
  phase-based large-block estimates, actual descents and uniform termination
  remain open. No external deep theorem is used in this checkpoint, and
  WeightedCapture and P0 remain unproved.

- F25 (2026-09-12): 852 checked declarations. Adds 42 core results: the
  3*N^2 vertical enlargement, exact original-label targets at all boundary
  rows, zero-extension energy preservation and exact original-block recovery,
  complete Gram pair/lag phases and the N^(-4) energy estimate. A
  large compressed original block yields at least N*v^2/4 nonzero lags with
  sums at least N*v^2/8 under the explicit threshold N*v^2>=2. The uniform
  theorem fixes c=v^2/8 and N0 before N, both profiles, masks and horizontal
  points. Each lag keeps its own actual original source root; other profile
  arguments may be outside the original box and require the supplied full
  field. An exact two-term obstruction refutes bounding a truncated sum by
  the complete sum's modulus. Two earlier reindexing theorems are generalized
  to arbitrary additive commutative monoids to handle complex sums directly.
  The full build and 852-theorem transitive audit pass with only standard
  foundations. No external deep theorem is used. Structural block counts,
  coefficient/denominator descents, realization and uniform termination
  remain open; P0 and WeightedCapture remain unproved.

- F26 (2026-09-12): 877 checked declarations. Adds 25 core results for full
  integer affine profiles: exact original-box and real-formula agreement,
  all four actual cubic phase coefficients, exact lag intervals and the
  existing cubic Weyl theorem on shorter intervals with original N normalization.
  Scale-explicit affine returns retain actual bounded-multiplier fibers.
  Both actual compressed-block directions give the current slope relation
  at N^(-4), keeping the exact factor 8*n1*n2. Many actual blocks then force
  a bounded positive multiple of the slope at N^(-5); the contrapositive
  gives the genuine no-relation count. For each s>0, uniform prior Q,E,N0
  control the original operator on these rows with norm <=s, for arbitrary
  pointwise contractive masks and the same input. A quarter-slope obstruction
  proves that the integer factor cannot simply be cancelled. The full build
  and 877-theorem transitive audit pass with only standard foundations and
  no new external input. Relation-row children, the degree-zero Fourier base,
  higher-degree and general structural counts, descents and termination
  remain open. Neither complete affine freezing nor WeightedCapture nor P0
  is proved at this checkpoint.

- F27 (2026-09-12): 886 checked declarations. Adds nine results: the exact
  circle error of the all-root major-arc grid, actual affine relation-row
  increments in cubic major arcs, globally defined constant-in-y children,
  their uniform count and original-point assignment, and full affine freezing
  conditional only on the precisely stated degree-zero core case. The offset
  list precedes all slope/intercept data and its size precedes N. Child profiles
  retain horizontal dependence and are not global original-frequency candidates.
  The s/3 no-relation budget, grid accuracy, J-dependent child tolerance and
  final cutoff/scale are selected in the correct order before N and coefficients.
  The full build and 886-theorem transitive audit pass with only standard
  foundations. UniformConstantFreezing is an unproved function premise, not
  an axiom or a completed external theorem. The degree-zero Fourier proof,
  higher-degree and general structural interfaces remain open, as do
  WeightedCapture and P0.

- F28 (2026-09-12): 909 checked declarations. Adds 23 results for exact
  vertical Fourier translation and fiber-energy transfer, a cyclic input
  injection and zero extension preserving all original endpoints and energy,
  and recovery of the complete original degree-zero response. Every cyclic
  character is represented by a single circle frequency for all powers, so
  the quadratic Fourier phase is retained. Probability-normalization factors
  cancel exactly; the original output restriction follows the full cyclic
  estimate. UniformHorizontalConstantFreezing implies the degree-zero target
  with unchanged Q,N0. The horizontal premise remains unproved and is not an
  external exemption. Its exact Gram and simultaneous coefficient estimates
  and actual large-entry count remain open. All 909 declarations pass the
  full build and standard-foundation audit. No new external deep theorem is
  used; WeightedCapture and P0 remain unproved.

- F29 (2026-09-12): 940 checked declarations. Adds 31 results for the actual
  horizontal cubic-plus-quadratic kernel, complete collision/interval labels,
  exact Gram phase coefficients, diagonal and trivial bounds, and scalar
  Schur with supported horizontal masks. The two-coefficient return retains
  the original current-row frequency and common positive multiplier. From
  the explicit CubicTwoCoefficientWeylInput, actual large-entry counts yield
  the uniform degree-zero estimate and complete affine freezing. There is
  no separate unproved core estimate among the final theorem's premises.
  The external analytic input and its library adaptation are not proved and
  are not declared as axioms. All 940 declarations pass the full build and
  standard-foundation audit. Higher-degree and general structural stages,
  WeightedCapture and P0 remain unfinished.

- F30 (2026-09-12): 966 checked declarations. Adds 26 results for genuine
  ordinary polynomial profiles, original response recovery, affine substitution
  coefficients, the exact full double-phase polynomial and its degree bound.
  For every D>=2 its degree-(D+2) coefficient is -3*k*(2*h)^D*a_D(x+h),
  independently of the original root and including zero/lower actual degrees.
  An exact D=1 example preserves the separate affine argument. The ordinary
  induction target and D=0,1 bases match F29. From PolynomialLeadingWeylInput,
  actual successful lag sums and proved affine recurrence give the current-row
  single-block N^(-(D+3)) return. The factor 3*2^D is retained and reversal is
  performed only on actual compressed blocks. All constants precede original
  data. The external input is neither proved nor declared as an axiom.
  Nonlinear h^D returns, higher-degree children/induction and general structural
  stages remain open. All 966 declarations pass the full standard-foundation
  audit. WeightedCapture and P0 remain unproved.

- F31 (2026-09-12): 985 checked declarations. Adds 19 results constructing
  actual degree-(D-1) ordinary polynomials from top-relation rows, with all
  original nonconstant lower coefficients, rational/circle branches and point
  assignments retained. The offset count precedes N and original coefficients;
  the error is epsilon/(2*N^3). A half-frequency obstruction valid for all D,N
  forbids zero-branch deletion. MonomialDenseReturns states the exact remaining
  INTERNAL core obligation, including m=D, and is not proved or exempted as an
  external deep theorem. Its D=1 instance and bounded-denominator adapter are
  checked. Conditional on this core premise and the external Weyl inputs,
  actual displacement counts give the no-relation operator and constructed
  children give complete natural-degree induction with the original responses
  and s/3, s/12, s/3 budgets. All 985 declarations pass the standard-foundation
  audit. Nonlinear returns and general structural stages remain open;
  WeightedCapture and P0 remain unproved.

- F32 (2026-09-13): 998 checked declarations. Adds 13 results proving dense
  monomial returns for all m>=D>=1, including the critical m=D case, with no
  unproved core or external premise. Actual integer buckets provide D+1
  original returns; rational interpolation clears integer denominators before
  the center is chosen, and finite relative patterns give uniform bounds.
  Exact same-sign retention and actual rounding fibers give the full power
  gain through integer diameter, without a derivative estimate near zero.
  The proved witness is substituted in F31: ordinary freezing in every fixed
  degree now has only the two explicit external Weyl premises. All 998
  declarations pass the standard-foundation audit. General structural
  models, realization, rational descents and uniform structural termination
  remain open. WeightedCapture and P0 remain unproved.

The historical twelve incorrect three-dimensional composite applications are
unused throughout. No change to the scope or status of U0 is asserted.
