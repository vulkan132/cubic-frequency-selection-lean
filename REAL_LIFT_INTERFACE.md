# Simultaneous real lift: checked interface at F16

Status: CHECKED through `uniform_original_real_lift`. The single lift, all
pointwise grid/error bounds, and the positive original weighted real-zero cube
mean have Lean proofs with only standard foundations. P0 and WeightedCapture
are still unproved; structural extraction and freezing remain separate.

The source read again at F16 is
`../GMZ_P0_Zenodo/sections/03-extraction.tex`, subsection **One simultaneous real
lift**, following `eq:circle-cubes`. The original complete-response and weight
contracts remain in force. The lift assertions below now have checked
implementations; the later interfaces listed at the end remain open.

## Checked input

`uniform_distinct_original_cube_capture` fixes positive M,c,a,d,E,N0 before N,
the cyclic modulus q, and all original f,theta,lambda,mu. For N>=N0 and prime
N^2<q<=128N^2, admissible original data give the same safe rectangle D, original
mass at least c, full weighted response at least eta*mu(D), and original
pointwise aligned response on nonzero weight support. Put

- sigma = N^3*mu*1_D, extended by zero in the cyclic vertical variable;
- ell = floor(a*N/64);
- v_omega = Y + 2*h*sum_i u_(i,omega_i), with h in the complete positive [N];
- epsilon_omega = (-1)^(number of true coordinates of omega).

The normalized average over x,h,Y and the eight independent shift coordinates
of the sixteen original sigma factors, restricted to injective omega -> v_omega
and

`||d * sum_omega epsilon_omega theta_x(v_omega)||_T <= E/N^3`,

is at least `(a/4)^16/4`. The Lean cubic coefficient has a leading minus sign;
the circle norm is unchanged by negation. No original pointwise frequency has
yet been captured. Nonzero cube weight gives actual retained original points
and the same complete original response at every vertex.

## Checked output and quantifier order

For each such fixed original input, `uniform_original_real_lift` constructs
**one function** F on all cyclic points, zero where the original weight vanishes.
That single F is shared by every cube; the quantifier is
`exists F, weighted mean of real-zero cubes >= beta`.
It is not permissible to replace it by a separate existential F inside each
cube's success condition. This F is a real lift auxiliary to the original
endpoint function f; f and its responses must stay unchanged.

Write `M_lift=floor(N^3/E)` to distinguish this grid denominator from the
already chosen horizontal-window integer M. After increasing the uniform
threshold, the checked theorem proves

- F_z in `(1/M_lift)*Z` for every point, and F_z=0 at zero sigma;
- |F_z|<=3 everywhere;
- `||F_z-d*theta_z||_T <= 19*E/N^3` on positive sigma;
- original weighted mean of the condition
  `sum_omega epsilon_omega F_x(v_omega)=0` **in R** at least
  `beta=((a/4)^16/4)*57^(-16)`.

The threshold and beta precede q and every original input. F may depend on
the fixed input. This intermediate dependency must not be confused with the
eventual finite candidate list, which must precede the original input.

## Checked construction

For each positive-sigma point, `frequencyUnitRep` fixes the representative
t_z of d*theta_z in [0,1), and `liftRound` sets n_z=round(M_lift*t_z). The global
assignment gives that point one pair of choices
U_z in {-9,...,9}, V_z in {-1,0,1}, and set

`F_z=(n_z+U_z)/M_lift+V_z`.

`CyclicLiftAssignments` is the full finite product of these 57 choices per
point. Each point's choice is reused whenever it occurs in another cube.
`LiftChoices` and `CyclicLiftValues` prove the grid, size and circle-error
estimates for every allowed global assignment.

For a successful cube, `cube_rounding_branch` produces integers l,r with

`sum_omega epsilon_omega n_(v_omega) = l*M_lift+r`, `|l|<=8`, `|r|<=9`.

These bounds are derived from the same rounded values, the original circle
cube condition, the eight positive/eight negative signs, and M_lift's floor
bounds. The branch l is the nearest integer to the actual rounded sum divided
by M_lift, and r is that sum minus l*M_lift. No branch is discarded.

An allowed local assignment sets U=-r at one positive vertex and zero at the
other fifteen; it sets V=-sign(l) at |l| of the eight positive vertices and
zero at the others. `exists_cube_lift_zero` proves its real alternating sum
is exactly zero. For l=0 the selected subset is empty, so the value assigned
outside it is zero as required. `assignmentSplitEquiv` gives a complete
bijection between global assignments and assignments on the distinct vertices
plus the complement. `cyclic_lift_cube_probability` therefore proves that the
actual event has probability at least 57^(-16).

`exists_global_weighted_success` exchanges the finite averages, keeping the
nonnegative product of all sixteen original weights, and chooses a global
assignment reaching at least the average success weight. `CyclicGlobalLift`
connects it to the actual cyclic real lift. Independence between different
cubes is neither supplied nor needed: they generally share points. Independence
is used only for the sixteen distinct point choices in a fixed cube.

`uniform_lift_grid_scale` chooses its threshold before q and the original data.
`uniform_original_real_lift` combines it with the original distinct-cube theorem
and retains the exact safe-window mass, weighted response and supported pointwise
responses. `separate_witnesses_not_one_global_witness` is an exact counterexample
to replacing one global choice by independent existential witnesses.

## Later interfaces remain open

The lift alone will not establish the paper's vertical-value proposition.
F17 has additionally checked exact frequency averaging on the complete mesh
j/1024, the actual local fourth moment and positive good-fibre proportion.
Family concatenation, the real approximate-polynomial theorem, nilpolynomial realization, uniform
operator freezing and the required external theorem implementations all remain
separate obligations. All circle root branches and vertical quadratic freedom
must continue to be retained.
