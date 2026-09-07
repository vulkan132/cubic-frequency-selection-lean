# Weyl interface audit, F17

The primary reference consulted is Green and Tao, *The quantitative behaviour
of polynomial orbits on nilmanifolds*, arXiv:0709.3562v6, sections 3 and 4:
https://arxiv.org/html/0709.3562v6#S4 . Lemma 4.4 is the highest-coefficient
inverse estimate; its induction uses differencing and linear recurrence.
Lemma 3.2 and Lemma 4.5 concern stronger recurrence. These references are not
Lean axioms and do not by themselves close the project's proof obligations.

The project's checked route has explicit formulas and hypotheses:

- `linear_interval_weyl_inverse`: for N>0, rho>0, arbitrary signed integer
  endpoints L,U and arbitrary circle a,b, a norm >=rho of the interval sum
  of e(t*a+b), divided by N, implies ||a||<=1/(2*rho*N).
- `weyl_mean_square_identity`: the complete mean square is expressed by every
  actual interval correlation, including h=0. The normalization is exact.
- `many_large_weyl_correlations`: if |F|<=1, the mean norm is >=rho>=0 and
  N*rho^2>=2, there are at least N*rho^2/4 nonzero signed shifts with correlation
  norm >=rho^2/8. This is proved from the pair-sum identity and finite counting.
- `weyl_small_scale_obstruction`: at N=1, the constant sequence has mean norm
  one and every nonzero shift correlation is zero. Thus the nonzero-shift
  assertion must not be imported as an unconditional all-scale statement.
- `quadratic_many_returns`: the actual quadratic sum yields a dense family
  with ||2*h*a2||<=4/(rho^2*N). This is an N^(-1) bound on shifted multiples,
  not the N^(-2) inverse conclusion for a2.
- `affine_return_small_multiple`: if a subset of [-N,N] has more than
  floor(2N/Q)+1 points, two actual returns in the same integer bucket give
  a positive integer q<Q with ||q*a||<=2*epsilon. The common intercept cancels
  by subtracting these actual returns.

The amplification is now proved by `uniform_affine_dense_returns`. For rho>0,
C>=0, choose Q=ceil(8/rho), K=ceil(2C+1), B=2K+1,
E=4*B*Q/rho, and N0=ceil(4*B/rho)+1. These choices precede all data.
If N>=N0, epsilon>=0, epsilon*N<=C, and at least rho*N elements of [-N,N]
satisfy ||h*a+b||<=epsilon, then some 1<=q<=Q satisfies
||q*a||<=E*epsilon/N.

The proof takes nearest real representatives u of q*a and v of q*b. It retains
all actual returns after multiplication by q. Their rounding integers lie in
[-K,K]. One rounding fiber has enough points that its integer diameter is
large; its two extreme values differ by at most twice the return error.
This supplies the inverse-N factor. No root of q*a is selected or discarded.

`uniform_quadratic_weyl` and `uniform_cubic_weyl` give, for each rho>0,
constants Q,E>0 before N and all circle coefficients, such that a complete
sum of norm >=rho has 1<=q<=Q and ||q*a_d||<=E/N^d, d=2 or 3.
Every N>0 is covered. In the cubic proof, quadratic estimates apply to the
actual overlap intervals with original N normalization; the next recurrence
step uses one dense fiber of actual successful quadratic denominators.

`uniform_cubic_common_denominator` replaces q by Q! uniformly. The estimate
is matched to the exact original cube time polynomial, and
`uniform_original_cube_capture` retains original weighted mass >=(a/4)^16/2
for ||D*cubeCoeff||<=E/N^3 with all constants before N,q and original fields.
Original safe mass and full responses are retained. This closes the highest-
coefficient Weyl and common-denominator selection interface of F13.

F15 has additionally checked exact k-average removal, full sign reflection,
and the 120/(2*ell+1) collision bound. One data-independent threshold leaves
original weighted distinct-vertex cube mass >=(a/4)^16/4 with full responses.
F16 has now proved a simultaneous global real lift with all grid and error
bounds, retaining weighted real-zero cube mass >=(a/4)^16/(4*57^16) and the
same original responses. F17 has checked exact frequency averaging, the actual
local fourth moment and a positive proportion of good (x,j) fibres. The next
step is local-to-global comparison and the local-four to global-seven family interface. The general nonlinear dense-return
lemma for h^n, n>1, and a simultaneous inverse estimate for all lower coefficients
are not asserted proved by these modules.

All coefficients remain on R/Z. No division selects a single root branch.
These auxiliary results neither prove P0 nor constitute a counterexample to P0.
