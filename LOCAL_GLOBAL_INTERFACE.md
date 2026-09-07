# Complete local-to-global comparison: checked at F19

F19 contains 677 audited theorem declarations. P0 and WeightedCapture remain
unproved. The local comparison below is now proved without the F18 residual
character-twist hypothesis; family concatenation remains open.

## Exact normalization and repetitions

For a finite parameter map r:A->G, the density relative to uniform measure on
G is nu(x)=|G|*card{a:r(a)=x}/|A|. Every representation is counted. For nonempty
A its uniform mean is one. Weighted averaging against nu exactly reproduces
the original parameter mean. Its difference density is w(d)=E_y nu(y+d)*nu(y).
The law of r(b)-r(a), with independent original parameters a,b, is exactly w.
Tensorization and translating the cube root by the first shifts give the exact
local cube moment. Fourier coefficients use E_x F(x)*conj(psi(x)); inversion
uses a character sum. The coefficients of w are |nu_hat(psi)|^2, nonnegative
with total mass E nu^2. Representation bound K gives E nu^2<=|G|*K/|A|.

## The completed comparison

`globalTwistedCubeMean_le` proves, for every finite abelian G, every complex
H, and every s>=2, that every global s-cube mean with twist product_i psi_i(d_i)
has modulus bounded by the untwisted global s-cube moment. Its proof uses
cross-correlation Fourier energy and a translation square-sum estimate for
s=2, followed by the exact cube derivative recurrence for higher dimensions.
No unproved mixed Gowers inequality is assumed. An exact ZMod 2 counterexample
shows the same claim fails for s=1.

Consequently `localCubeMoment_le_global` proves, for all s>=2,

    local s-moment <= C^s * global s-moment,

from E nu^2<=C. `localCubeNorm_le_global` gives the corresponding exact
iterated-square-root constant. `globalCubeMoment_lower_from_local` gives

    rho^(2^s)/C^s <= global s-moment

when C>0, rho>=0 and rho<=the local s-norm. This comparison does not require
||H||<=1, although that bound is needed for the later family and deletion steps.

## Exact seventh-moment return to the original real field

`global_frequency_moment_exact` identifies the complete mesh average of the
global s-moment with the weighted real-zero cube mass for every 1<=s<=7.
`cyclicGlobalSeventhMoment_eq_mass` applies it to the same fixed lift F and
the actual cyclic original weight. All 128 factors and all repetitions remain.
This equality does not assert a positive lower bound.

## Remaining work

Prove the uniform family concatenation theorem and the actual exceptional-pair,
representation-count and no-wrap estimates. Then derive a positive seventh
moment uniformly from the checked good (x,j) fibres, preserving the same F,
all prior constants, original mass, and original full responses. Real structural
extraction, realization and uniform freezing remain subsequent open interfaces.
See CONCATENATION_SOURCE_AUDIT.md and PAIR_GEOMETRY_PROOF_PLAN.md.
