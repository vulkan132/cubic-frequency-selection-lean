# Open mathematical interfaces after F19

Full P0 formalization is still unfinished. No item below is a project axiom.

## What the checked terminal theorem actually requires

For a fixed denominator bound Q and accuracy epsilon, the checked theorem
finite_capture_from_model_operators constructs a length L before N and a list
beta before all original and model data. It requires a retained set A with
original mass at least c, original aligned response at least eta, a finite
family p_i and an arbitrary pointwise assignment iota satisfying

- d_(3,N)(theta_z, p_(iota(z))(z)) <= epsilon/2 on A;
- every p_i satisfies FiniteMinorEstimate at
  s = eta*sqrt(c)/(8*sqrt(J)).

Its conclusion retains A' inside A, original mass at least c/2, and full-label
distance at most epsilon to a listed constant. The proof of these implications
does not prove that such models or operator bounds exist.

FiniteMinorEstimate is the actual squared bound for all finite input vectors g.
The finite input box is [2N] x [2N^2], and endpoint_eq_inputPoint and
finiteResponse_original prove that restriction of the original f gives exactly
the original complete response. No artificial response is substituted.

## Checked original local fourth moments; next, comparison and concatenation

Read the original sections 2 and 3 when implementing these steps, preserving
the inner-product convention linear in its first variable.

The finite adjoint identity, original endpoint Gram expansion and I/N diagonal
block are now checked. The first adjoint lower bound keeps the exact original f
and b_z = sigma_z*conj(lam_z). Its h=0 contribution is exactly ||b||²/N, bounded
by sum(sigma)/N. Restricting sigma = N³*mu*1_D preserves the exact original mass
and support; positivity is used only at nonzero weights.

The complete horizontal grouping proves original_window_first_tt:
sum_(x!=x') |J_(x,x')| >= N³*max(|R_D|²/4-m/N,0), with m = mu(D).
The second adjoint now explicitly restricts both horizontal coordinates to X.
For D whose horizontal support is contained in X, the checked original finite
statistic S_fin satisfies max(|R_D|²/4-m/N,0)² <= S_fin+m/N. Its second diagonal
is nonnegative and bounded by m/N after normalization, separately from h=0.
Nonparallel collision uniqueness gives exact N^(-2) nonzero kernel entries and
the N^(-3) row energy bound. Both sigma factors and both alignment phases are
preserved in finite_signed_original_weights.

The explicit X restriction is essential: outside first pairings vanish because
of support, but their second adjoint energies need not vanish. The exact theorem
zero_pairing_nonzero_adjoint witnesses that distinction. None of the checked
estimates infer zero adjoint energy from a zero pairing.

The safe-window construction is now checked, with M=ceil(64/kappa), H=floor(N/M)
and c=kappa/(4M)>0. Boundary deletion loses at most 6H/N<=kappa/8 in the original
weight; the count also handles overlapping strips. A partition into at most M
intervals of diameter H produces D=X times safeRows with original mass at least c.
The interval bounds are exact, including partial final blocks. Target displacement
bounds and actual original finite target indices are also checked.

uniform_positive_safe_statistic fixes M,c,zeta,N0 before N,f,theta,lam,mu and then
selects D and X for every admissible input. It proves S_fin>=2*zeta>0, keeping
the same original f, theta, both weight factors and pointwise response on the
nonzero original weight support. The construction uses
zeta=eta^4*c^4/256 and N0=ceil(128/(eta^4*c^4))+1.
The complete single-block formula and two-label Gram-row formula are now
checked. A valid first label has one original target; each valid second label
has an injective canonical source y+2h(r1-r2). Every original collision is
included once. The map (r1,r2) to (k=r1-r2,r=r2) is a proved finite-sum
bijection, and unequal labels correspond precisely to k!=0 when h!=0.
The circle phase, both original weights and both alignment factors are exact.

finiteSignedDoubleStatistic_eq_lag proves equality of the whole finite
statistic with lagSignedDoubleStatistic at total scale N^(-6). The latter
is the explicit finite presentation with x,x' in X, x'!=x, every original y,
k in [-N,N], r in I_h intersect (I_h-k), and k!=0. Larger lags have empty
label sets. The integer-coordinate field extension agrees at every supported
original source/target, and the weight extension is zero outside the box.
uniform_positive_safe_lag_statistic transfers the same uniform positive lower
bound and original response to this lag sum. This closes the lag reindexing
interface of F06; it does not prove any subsequent averaging estimate.

The whole-sum t=r+k-h reindexing is now checked by lag_sum_reroot. Its outer
labels are exactly t,t+h in [N], and its inner interval is K_(h,t). The actual
k=0 summand is sigma_z^2*|lam_z|^2. The complete zero-lag statistic is nonnegative
and at most mu(D)/N under the original weight and unit-alignment hypotheses.
This is a direct bound on the reinserted lag sum, separate from the h=0 error.

originalLagSummand_reroot gives the exact g(k)e(P(k)) factorization on the same
original fields. B is normalized by N, not by the interval's actual cardinality.
signed_plus_diagonal_reroot proves S_lag+D_lag=N^(-5)*rerootedWeightedSum.
Both |g| and |B| are at most 1, and the real-part-to-modulus passage keeps the
nonnegative original weight. finiteRerootedNormAverage enumerates all original
x,x',y,t finite indices, retaining the exact window and t+h indicators.
uniform_positive_rerooted_average gives this average at least 2*zeta with all
constants chosen before N and the original data; mass and response are retained.

The cyclic conversion is now checked. cyclicRow is injective when N^2<q;
its range is exactly the residues with representatives in [1,N^2]. The weight
vanishes outside that range. Safe supported lag and shared-target evaluations
have no wraparound, so the cyclic g,P,B agree exactly with the original ones.
The complete weighted vertical sum and the x' to h reindexing are proved.
horizontalShiftLabels has exactly 2N elements, including zero-contribution
shifts which do not reach X.

finite_to_cyclic_modulus_average proves that the original finite modulus
average is (2q/N^2) times cyclicModulusAverage. The proof passes to moduli in
the original finite domain before this exact conversion. The resulting
cyclic expression is a uniform mean on the explicit 2qN^3-point space, with
weights in [0,1]. Bounds |g|,|B|<=1 hold on the entire cyclic group and all
integer parameters, including those reached during subsequent smoothing.
uniform_positive_cyclic_average chooses M,c,zeta,N0 before N,q and all data;
for every N^2<q<=128N^2 it retains the original safe mass and response and
proves a cyclic mean at least zeta/128. This step does not require primality.
exists_prime_cyclic_modulus supplies 64N^2<q<128N^2 from the checked Mathlib
Bertrand theorem, without an added mathematical axiom.

Interval translation is now checked for every integer shift, every bounded
complex sequence and all integer intervals, including empty intervals. The
actual lag interval is an Icc, and its N-normalized translation costs at most
2*abs(d)/N. FourShiftSpace is the full Cartesian product of four copies of
[-ell,ell], with cardinality (2*ell+1)^4 and total shift at most 4*ell.
The complex mean commutes exactly with the whole k sum. Its error is at most
8*ell/N, at most a/8 for ell=floor(a*N/64), including ell=0.

uniform_positive_smoothed_average now fixes M,c,a,N0 before N,q and all original
data. It retains the safe window's original mass, original weighted response
and pointwise aligned response, while giving the actual smoothed weighted mean
at least 7*a/8. The weight is not removed at this stage. The exact
cyclicSmoothedLagB_four_faces identity expresses the original cubic phase as
four unit circle factors. cubicFacePhase_independent proves that factor i
does not depend on coordinate i. All operations stay on R/Z; no real lift or
root selection is made.

The box estimate is now proved separately. box_cauchy_schwarz is an induction
for every dimension d=n+1: exact coordinate doubling removes one unit face
factor and preserves the independence and unit modulus of all remaining
factors. The base is the one-dimensional squared mean. The recursively defined
boxMoment is nonnegative, and boxNorm^(2^d)=boxMoment is an exact identity.
cyclicShiftMean_le_boxNorm applies this theorem to the actual four-shift
function, using the previously checked cubic factors on the full shift space.

cyclicSmoothedModulusAverage_le_three_boxMean removes the original outer
weight only from a nonnegative box norm, extends the lag sum to [-N,N], and
uses the exact ratio (2N+1)/N<=3. The full outer space is
CyclicSamplingSpace N q times fullLagLabels N, of size 2qN^3(2N+1).
The finite moment inequality (proved by repeated squared-mean Cauchy–Schwarz)
gives cyclicBoxNormAverage^16 <= cyclicBoxMomentAverage.
uniform_positive_box_average fixes M,c,a,N0 before N,q and all original data,
retains the original safe mass, weighted response and pointwise response,
and proves cyclicBoxMomentAverage >= (a/4)^16. Its input is exactly the actual
cyclic g built from original fields.

cubeMean_eq_boxMoment now proves equality in C with the full Boolean-vertex
product in every dimension. Parity conjugation, all coordinate-pair means and
multiplicities are retained. In dimension four the pair space has
(2*ell+1)^8 points. cyclic_cube_expansion applies this equality to the actual
original cyclic g. cyclicCubeAverage_reroot performs the entire Y=y+2hk change
of variables by an explicit finite equivalence, without dividing by 2h.

cyclicRerootedCubeProduct_factorized separates the sixteen-weight product,
the alternating original alignment product, and a circle character. The weight
lies in [0,1], and the alignment has modulus one. cyclicCubePhase_polynomial
proves the full cubic t-polynomial identity in R/Z. Its top coefficient is
cyclicCubeCubicCoeff = -sum_omega cubeSign(omega)*theta(v_omega), with no k or t
argument. The weight and alignment likewise have no k or t argument.

cyclicRerootedCubeAverage_split_time uses a complete finite bijection to put
the full Fin N time average innermost. Its other parameter space has size
2qN^2(2N+1)(2*ell+1)^8. uniform_positive_weighted_time_average retains original
safe mass and complete response while proving the original sixteen-weight
average of the time-sum norm is >=(a/4)^16. All constants precede N,q and data.
cyclicCube_original_vertices proves that every vertex of a nonzero-weight
cube corresponds to an actual point of D with nonzero original mu, matching
theta/lambda/N^3*mu field values and the original complete response.

Linear inverse Weyl is now checked, including an arbitrary integer interval
normalized by the original N: a mean norm >=rho gives ||a||<=1/(2*rho*N).
The finite pair-sum identity and the h=0 bound prove at least N*rho^2/4
nonzero signed shifts with correlation norm >=rho^2/8 when N*rho^2>=2.
The N=1 counterexample shows why a threshold is needed. Quadratic and cubic
differences retain the actual overlap interval and all circle coefficients.
quadratic_many_returns gives the dense set of shifts with
||2*h*a2||<=4/(rho^2*N). The missing recurrence improvement is now proved:
uniform_affine_dense_returns gives ||q*a||<=E*epsilon/N when epsilon*N<=C,
with Q,E,N0 before N,a,b,epsilon and the retained set. Its finite rounding-fiber
proof uses only actual return values and the integer diameter of a dense fiber.

uniform_quadratic_weyl and uniform_cubic_weyl now give the respective N^(-2)
and N^(-3) highest-coefficient estimates at every N>0. Actual shorter intervals
are rescaled exactly; a large original-N-normalized sum forces a sufficiently
long interval. Cubic differencing retains a dense fiber of actual positive
quadratic denominators before its second recurrence amplification.

uniform_cubic_common_denominator uses the factorial of the uniform bound,
fixing one positive D before N and all circle coefficients. The exact original
time polynomial is matched by cyclicCubeTimeAverage_as_polynomial.
uniform_original_cube_capture proves original weighted cube mass >=(a/4)^16/2
on the condition ||D*cubeCoeff||<=E/N^3. M,c,a,D,E,N0 precede N,q and every
original input. The same safe-window mass, full weighted response and supported
pointwise original responses remain in its conclusion. This is a cube-coefficient
statement, not a capture of the original pointwise theta or a global real lift.

The unused k average is now removed by a finite bijection, with no loss.
Simultaneous h/shift reflection fixes every actual vertex, giving exact equality
to the positive-h mean. Resampling one of the eight independent shift coordinates
proves that distinct labels collide with probability at most 1/(2*ell+1), provided
the short interval embeds and 2h is nonzero modulo the prime q. The union over
all 120 unordered pairs gives 120/(2*ell+1). A separate exact q=7,h=7,ell=1
counterexample shows why an integer h!=0 does not replace the modular condition.

uniform_collision_scale fixes a threshold before q and all original data,
guaranteeing both modular hypotheses and any positive collision budget.
uniform_distinct_original_cube_capture retains mass >=(a/4)^16/4 of successful
sixteen-distinct-vertex cubes, together with the same original safe-window mass,
complete weighted response and supported pointwise responses.

uniform_original_real_lift now supplies one F on all cyclic points, with every
point's choice shared by all cubes. Its grid is M_lift=floor(N^3/E)>=9, |F|<=3,
and F=0 on zero original weight. The supported error to d*theta is <=19*E/N^3.
The same rounded integers have a branch l and remainder r with |l|<=8, |r|<=9;
an allowed local correction makes the real fourth difference zero. Restriction
of the global choice product to distinct vertices is uniform, giving probability
>=57^(-16). Exchanging finite weighted averages gives one global F with real-zero
cube mass >=(a/4)^16/(4*57^16). All constants precede N,q and every original
input, and all original safe mass and complete responses remain in the theorem.
See REAL_LIFT_INTERFACE.md for the checked construction and exact scope.

Exact frequency averaging is now checked. The complete j/1024 mesh detects
real zero for all grid cube differences of dimensions at most seven, with an
explicit 384*M bound. All original weights factor exactly. The actual local
fourth-norm sixteenth moment equals the checked weighted real-zero cube mass.
`uniform_original_local_fibres` also gives a proportion >=beta/2 of actual
(x,j) pairs with mean_h local norm >=beta/2, for the same fixed F and with all
original responses retained. See FREQUENCY_AVERAGING_INTERFACE.md.

The multiset local-to-global comparison is now checked for s>=2. Next prove the precise family
concatenation theorem, then global seventh moments. The large-block operator
estimate remains pending.

The checked expansion convention is section 2, eq:local-norm: two independent
copies of each coordinate, a product over all Boolean vertices, conjugated at
odd parity, with multiplicities retained. Coincident vertices must not be
deleted during this equality; the later quantitative collision removal is
now proved separately. The cyclic rerooting is translation by 2hk with inverse
translation by -2hk, so that bijection itself requires no inverse of 2h. The
collision estimate does use the separately proved modular nonvanishing and
prime-field cancellation hypotheses.

The existing PhaseAlgebra identities alone do not establish any operator estimate.

## Structural extraction and realization

The paper's vertical-value proposition remains unformalized. In particular,
the following have not been discharged: actual pair geometry,
family concatenation, the real
approximate-polynomial input, and real nilpolynomial realization with all
lattice and circle branches. The simultaneous global real lift, exact mesh and original local fourth-norm
average are now checked; they do not imply these later statements on their own.
Quantifiers and uniform complexity bounds must be taken from the actual source
statements and original contracts, not from this task history.

## Uniform freezing

The conditional finite estimate must still be established for the paper's
fixed rational polynomial observation structures, uniformly over unrestricted
real coefficients and arbitrary horizontal dependence. This includes the
ordinary polynomial starting case, the rational polynomial module, the
semidirect-product observation, forced relations, all descents, and uniform
termination with compatible error budgets.

## External dependencies

Green–Tao, Tao–Ziegler and Manners statements must be exactly stated and proved,
or linked to actual checked implementations with matching hypotheses.
A keyword/path search of the pinned Mathlib v4.33.0 source at F03 found basic
nilpotent group/Lie-algebra modules but no directly callable implementation
identified by Gowers, nilmanifold, nilpolynomial, Tao–Ziegler or Manners.
This search is an inventory clue, not a proof of global nonexistence of such libraries.

The global goal remains a proof of P0 with no unproved mathematical premises.
An implication whose input is WeightedCapture or FiniteMinorEstimate does not
by itself meet that goal. U0 is unchanged; all twelve deferred erroneous
three-dimensional composite applications remain unused.

## F18 local comparison progress

The parameter density and its actual difference law, all-dimensional product
pushforward, exact local cube rerooting and nonnegative finite Fourier expansion
are checked. `localCubeMoment_bound_of_twisted` still explicitly requires the
uniform character-twisted cube bound. Removing that premise is the next step;
the full local comparison and the family concatenation theorem remain open.
See LOCAL_GLOBAL_INTERFACE.md and TWISTED_CUBE_PROOF_PLAN.md.

## F19 completed comparison and exact seventh-moment identity

The residual twist premise recorded in the historical F18 update above has
been proved for all s>=2 and eliminated from localCubeMoment_le_global.
The root norm comparison and explicit positive lower-moment implication are
checked. The exact dimension-one obstruction is also checked. Global complete
mesh averaging, including the actual cyclic seventh moment, equals the weighted
real-zero cube mass of the same F. This identity alone supplies no positive
lower bound. Family concatenation and actual pair geometry are now the immediate
remaining interfaces; see LOCAL_GLOBAL_INTERFACE.md.
