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

The historical twelve incorrect three-dimensional composite applications are
unused throughout. No change to the scope or status of U0 is asserted.
