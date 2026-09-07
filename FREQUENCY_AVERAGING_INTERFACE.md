# Exact frequency averaging: checked interface at F19

Status: exact finite mesh, original local fourth moment, and positive good-fibre
proportion are checked. Local-to-global comparison and family concatenation
remain OPEN. The source read again at F17 is `../GMZ_P0_Zenodo/sections/03-extraction.tex`, from
**Exact frequency averaging and concatenation** through `eq:seven-cubes`, and
the local norm convention in `sections/02-preliminaries.tex`.

## Checked input

`uniform_original_real_lift` produces one F shared by all cyclic points and
all cubes, with M_lift=floor(N^3/E)>=9, F in M_lift^(-1)Z, |F|<=3, and F=0
where the extended original weight vanishes. On positive weight,
`||F-d*theta||_T <=19*E/N^3`. The four-dimensional real-zero cube average,
with all sixteen original weights, is at least
`beta=(a/4)^16/(4*57^16)>0`. All constants and the threshold precede N,q and
the original input. The original endpoint function f and its full responses
are still present in the same theorem.

## Checked exact finite mesh

`realSignedCubeSum_grid_bound` proves for every d<=7, M>0, grid-valued F and
|F|<=3 that Delta^d F=k/M for an integer k with |k|<=384*M<1024*M. Every vertex
occurrence is included; distinctness is not required. The definition uses the
existing signed cube convention.

`rational_character_orthogonality` proves the complete geometric-sum identity
for |k|<B, B>0. With B=1024*M and alpha_j=j/1024, j=0,...,B-1,
`frequencyMeshMean_realCube` detects equality Delta^d F=0 in R exactly.
`integer_frequency_alias_obstruction` proves that all integer frequencies give
phase one for the nonzero real difference 1. `frequency_mesh_size_obstruction`
proves that the complete mesh still gives mean one for the nonzero grid value
1024 if the size condition is removed. These are obstructions to incorrect
intermediate rules, not counterexamples to P0.

`weighted_real_cube_character` factors the product of all original real weights
and the character of the actual signed real sum. `weighted_frequency_cube_real`
applies exact mesh orthogonality to the complete product, for all d<=7.

## Checked actual local fourth norm

`localCubeMoment n H r` averages the already proved (n+1)-dimensional box
moment over the group base Y, using the shift map r from a finite parameter
space. The shift map need not be injective, so multiset multiplicities are
sampled exactly. `localCubeNorm` is its iterated square root; nonnegativity,
the exact power 2^(n+1), and the bound <=1 for 1-bounded H are proved.

`localBoxFunction_cyclic_vertex` identifies each actual vertex for
r(v)=2*h*v mod q, v in [-ell,ell]. No division by 2*h is used.
`cyclicLocalFourthNormAverage_eq_mass` proves

`E_(x,j,h) ||sigma_x*e(alpha_j*F_x)||_(U^4_(2h[-ell,ell]))^16
 = cyclicRealCubeMass N q ell sigma F`.

The finite means over j,Y,shift pairs and h are exchanged explicitly. All
sixteen original weights, all repeated vertices and every shift multiplicity
are preserved. `uniform_original_local_four` applies the identity to the same
F supplied by the simultaneous lift, giving the original lower bound beta.
Its constants precede N,q and all original data, and the same safe mass and
complete original responses occur in the conclusion.

`bounded_moment_good_fibres` proves the finite bounded-moment density step.
`uniform_original_local_fibres` retains the entire preceding conclusion and
adds that a proportion >=beta/2 of actual pairs (x,j) have mean_h local fourth
norm >=beta/2. The function F is fixed before selecting these pairs; there is
no new lift for each auxiliary frequency. This is the checked input for the
family step. The family in the next theorem is indexed by the positive h labels. The same
modulus must also work for every bounded H_(x,j), hence for every j on the
growing mesh. The successful pair (h,h') may depend on (x,j); the constants
and all scale thresholds must not.

## Subsequent family step remains separate

The paper next requires a correctly normalized local-to-global Gowers norm
comparison for a multiset R. Its probability density nu_R is relative to
uniform measure on the finite cyclic group. The intended implication is

`||nu_R||_2^2<=C  =>  ||H||_(U_R^s)^(2^s)<=C^s*||H||_(U^s)^(2^s)` for s>=2.

This requires finite Fourier inversion, the nonnegative Fourier coefficients
of the difference density, and Gowers Cauchy--Schwarz with the exact linear
twists. None is supplied merely by the already proved box inequality.

The Tao--Ziegler family theorem must then be stated and proved with its actual
dependencies before using its contrapositive. Further required proofs include
the small-h and large-gcd exceptional-pair counts, a successful pair outside
them, integer representation multiplicity, and the density L2 bound.

For the no-wraparound count, use an actual prime in the already proved strict
range 64*N^2<q<128*N^2. The weaker lower bound N^2<q in the lift theorem alone
does not justify absence of collisions between arbitrary values in (-N^2,N^2).
Also derive every needed bound on a and floor(u*ell); the current lift theorem
records only a>0, so an upper bound on a must not be assumed silently.

After those steps, a uniform global U^7 moment and a second use of the exact
mesh should give positive original weighted real-zero seven-cube mass. The
real approximate-polynomial theorem and nilpolynomial realization remain
additional obligations, followed by uniform freezing. No part of this note
proves P0, captures the original theta, or authorizes removing circle roots or
vertical quadratic freedom.

F18 update: finite Fourier analysis, actual multiset parameter/difference densities,
all-dimensional product pushforwards and the exact positive-coefficient local
moment expansion are checked. The character-twisted global cube bound remains
an explicit premise; see LOCAL_GLOBAL_INTERFACE.md. The family theorem and
actual pair geometry have not yet been formalized.

F19 update: the full multiset comparison for s>=2 now has no unproved twist
premise. Complete mesh averaging of every global s-moment, 1<=s<=7, is also
checked, including the exact cyclic seventh-moment/original-weight identity.
The positive lower bound still requires family concatenation and actual pair
geometry. The F18 remaining-premise description above is historical.
