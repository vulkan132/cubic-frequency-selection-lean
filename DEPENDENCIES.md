# Proof dependency ledger

Paper theorem labels are source references, not evidence of correctness.
Current checked scope is recorded in STATUS.md and verification/result.json.
Definitions of targets are checked; target propositions are still unproved.

| Component | Source | Formal status / remaining obligation |
|---|---|---|
| Exact P0 statement | thm:p0 | Exact statement and WeightedCapture -> P0 checked; P0 remains unproved |
| Weighted capture statement | thm:capture | Universal list precedes data; positive original mass; all labels |
| Cubic average and distance | eq:average, eq:metric | Definitions, phase formula, cardinality, triangle and scaled circle bound checked |
| Response comparison | eq:comparison | Cauchy–Schwarz, original response transfer and circle scale bound checked |
| Finite selection | final subsection of section 5 | Fully quantified reduction from weighted capture to P0 checked |
| Circle roots and real grids | eq:root-profiles, eq:constant-grid | All root branches, rounding and data-independent major-arc list checked; its index cardinality has no N argument |
| Original input and energy | eq:average, eq:minor-energy | Exact endpoint embedding, response equality, input energy and finite-assignment energy checked |
| Terminal capture | eq:major-mass through eq:capture | Complete conditional model/operator-to-capture passage checked; existence of its premises remains open |
| Finite adjoint and first Gram identity | eq:block; section 3 before eq:first-tt | Exact endpoint Gram expansion, adjoint convention and I/N same-horizontal block checked |
| Original weighted first TT* | eq:first-tt | Original window mass, response, energy lower bound, exact h=0 split and grouped block lower bound checked |
| Second finite adjoint | eq:double-tt-lower, before lag reindexing | Explicit X, grouped Cauchy–Schwarz, nonparallel collision uniqueness, row energy, separate normalized diagonal bound and finite signed lower bound checked |
| Safe window | section 3 first subsection | Uniform positive original mass, exact integer interval partition, strip budget and supported original target indices checked |
| Positive finite and lag statistics | eq:signed-statistic; eq:double-tt-lower | Uniform constants and threshold precede all data; exact S_fin=S_lag>=2*zeta and original responses checked |
| Single block and lag statistic | eq:block, eq:double-phase, eq:signed-statistic | Complete single/double-label formulas and (r1,r2) to (k,r) finite-sum bijection checked; original targets, both weights, k=0 and N^(-6) normalization retained |
| Whole-sum rerooting and zero lag | eq:lag-phase; section 3 before normalization | Full t=r+k-h sum bijection, exact inner interval, original g(k)e(P(k)) factorization and explicit nonnegative k=0 sum <=mu(D)/N checked |
| Original finite modulus average | before eq:box-lower | Exact N^(-5) outer normalization, |g|,|B|<=1 and uniform positive original weighted finite average checked |
| Cyclic averaging | section 3 normalization | Original supported field/B identities, complete horizontal/vertical reindexing and exact modulus-average factor 2q/N^2 checked; uniform positive cyclic mean on 2qN^3 points with weights in [0,1] |
| Prime modulus | section 3 choice of K | Strict 64N^2<q<128N^2 range proved for every N>0 from checked Mathlib Bertrand |
| Four-shift smoothing | section 3 before eq:box-lower | Signed interval errors, full independent sampling, N normalization and >=7a/8 original weighted smoothed mean checked with uniform constants and original responses |
| Cubic face factors | section 3 before eq:box-lower | Four explicit unit circle-phase factors and their coordinate independence checked; exact whole smoothed expression |
| Box Cauchy–Schwarz | section 3 before eq:box-lower | Iterated inequality proved in every dimension; exact duplication and unit-face independence; nonnegative recursive box moment and root-power identity; actual four-shift application |
| Positive box moment | eq:box-lower | Weights removed only after nonnegativity; full lag ratio <=3; Jensen and uniform >=(a/4)^16 recursive box moment checked with original mass and response |
| Full cube expansion | eq:local-norm and after eq:box-lower | Exact complex equality with Boolean products, parity conjugation and multiplicities checked in every dimension; actual sixteen-vertex expansion and cyclic rerooting checked |
| Cubic t-average separation | section 3 before eq:circle-cubes | All sixteen original weights and alternating alignments factored; exact t polynomial and k-independent top coefficient; complete t-average reindexing and uniform weighted positive bound checked |
| Original cube vertices | section 3 original-field convention | Every nonzero-weight vertex is an actual retained original base point with matching fields and original full response |
| Linear inverse Weyl | section 2, eq:weyl, degree one | Geometric identity and inverse chord bound checked; all affine intercepts and actual integer intervals, original N normalization |
| Weyl differencing | one-variable inverse Weyl proof | Exact finite pair-sum identity, separate h=0 bound, nonzero-shift count with explicit threshold, and N=1 obstruction checked |
| Polynomial derivatives | one-variable inverse Weyl proof | Exact quadratic/cubic circle derivatives and actual overlap intervals checked; dense quadratic leading multiples established |
| Quadratic/cubic inverse Weyl | section 2, highest-coefficient eq:weyl | Proved at every positive scale with uniform bounded positive denominators; exact shorter-interval rescaling and actual denominator fibers checked |
| Common denominator and weighted selection | section 3, before eq:circle-cubes | Factorial denominator fixed before N and all data; exact original cube coefficient and weighted mass >=(a/4)^16/2, original responses retained |
| Circle cube extraction | eq:circle-cubes | Exact k removal and simultaneous sign reflection checked; positive-h mean preserves all weights and coefficients |
| Distinct cube vertices | section 3 before eq:real-four-cubes | Short interval injection, modular nonzero step, single-coordinate pair collision bound, complete 120-pair union and weighted deletion checked; one uniform threshold preserves original weighted mass >=(a/4)^16/4 and full responses |
| Simultaneous real lift | eq:real-lift-error, eq:real-four-cubes | Checked: one global choice shared by all cubes, actual l/r branches, success probability >=57^(-16), M_lift grid, size <=3, supported d*theta error <=19E/N^3 and real-zero weighted mass >=(a/4)^16/(4*57^16); uniform constants and original responses retained |
| Exact frequency averaging | eq:orthogonality, eq:local-four | Checked: complete j/1024 mesh for all d<=7 with integer/size bounds, exact weighted real-zero detection, actual local fourth moment identity, uniform positive moment and good-fibre proportion with one F and original responses |
| Local-to-global Fourier reduction | eq:local-global | Complete for s>=2: exact density law, positive Fourier expansion, character-twist bound, moment/norm comparison and positive lower-moment consequence checked; no residual twist premise |
| Pair-geometry prerequisites | after eq:tz | Checked: actual local-four bound implies a<=256; uniform shrink threshold, short-radius, integer range and modular no-wrap lemmas for paired shifts; representation multiplicity and exceptional-pair count remain pending |
| Large-block operator estimate | eq:large-block | Full quantitative operator bound pending |
| Vertical value extraction | prop:values | Original weighted circle cubes, one global lift, exact mesh and local fourth moments checked; complete local-to-global comparison and exact global seventh-moment averaging checked; concatenation, actual pair geometry and real structural extraction remain pending |
| Finite realization | lem:realization | Correct lattice carry and unrestricted coefficients |
| Uniform freezing | thm:freezing | Full operator proof, rational modules, finite uniform descent |
| Dense returns | lem:returns | Affine recurrence amplification checked for epsilon*N<=C, with constants and threshold before data; nonlinear h^n recurrence versions are not asserted proved |
| Tao–Ziegler family theorem | eq:tz | Exact external theorem statement and formal proof |
| Manners approximate polynomial theorem | section 2 | Exact real-value statement and formal proof |
| Manners coordinate/lifting results | section 5 | Formal dependencies C.16, C.17, C.19 and definitions |
| Green–Tao equidistribution | section 2 and section 4 | One-parameter theorem and coordinate lemmas |

The main target will not be exported as a proved theorem by assuming weighted
capture, freezing, or any external result as an unnamed or new global axiom.
