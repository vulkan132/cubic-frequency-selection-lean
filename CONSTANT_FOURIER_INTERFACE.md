# F28: the degree-zero Fourier passage

The Fourier passage in the ordinary-polynomial starting case is now checked.
The horizontal minor-arc estimate itself remains an unproved core target.
No external deep theorem is introduced or proved in this checkpoint.

## Exact operators and quantifiers

For arbitrary phi : Fin N -> R/Z and every xi : R/Z, the horizontal operator is

    H(phi,xi)u(x) = N^(-1) sum_{r=1}^N u(x+r) e(phi(x)*r^3 + xi*r^2).

Its finite input has exactly 2*N horizontal coordinates. The coefficient
phi is constant only in the vertical variable, not in x. The checked
cyclic_character_frequency represents each cyclic character by one circle
frequency for all natural powers simultaneously. Thus the quadratic Fourier
term is retained in every summand; xi is not set to zero.

UniformHorizontalConstantFreezing states precisely:

    for every 0<s<=1, there exist positive Q,N0 such that
    for every N>=N0, phi, xi and horizontal input u,
    sum_x |1_{phi(x) outside MajorArc(Q,N)} H(phi,xi)u(x)|^2
      <= s^2 sum_t |u(t)|^2.

This is a definition of the remaining core proposition, not an asserted
theorem or a new axiom. uniform_constant_freezing_of_horizontal proves that
this proposition implies UniformConstantFreezing, with the same Q and N0.
Together with F27, it therefore suffices for complete affine freezing.

## Original input and normalization

The proof uses a finite cyclic group with q >= 2*N^2 and q nonzero. Original
vertical indices 0,...,2*N^2-1 are injected as their natural residues. The
original integer coordinate remains index+1. Values outside this input image
are zero. The injection, zero-extension recovery and equality of counting
energies are proved, not assumed.

Every original endpoint satisfies the exact index identity

    source_index + r^2 = endpoint_index in ZMod(q).

The endpoint index is still below 2*N^2, so no original input values are
identified. cyclicConstantResponse_original proves equality to the complete
original finiteResponse, for all original sources including the boundaries.
Via the existing finiteResponse_original theorem this is the same original f.

The Fourier coefficients use the probability mean and conjugate characters.
The checked translation formula has the positive multiplier psi(d) for the
shift y+d. Parseval is applied to the full cyclic input and output. The common
factor 1/card(G) cancels exactly when returning to counting energies. There
is no modulus-dependent loss or extra constant.

The proved generic translation theorem permits arbitrary horizontal masks,
since the coefficients are independent of the vertical variable. The actual
minor mask depends only on phi(x). After the full cyclic estimate, output is
restricted to the original N^2 vertical coordinates by a proved contraction.
No arbitrary vertical mask is silently treated as Fourier-diagonal.

The final finite estimate uses the deterministic modulus q=2*N^2+1. This
choice depends only on N; it requires no prime or external number-theoretic
input and changes neither the cutoff nor the scale threshold.

## F29 follow-up: horizontal core now checked from the external input

F29 proves the exact horizontal Gram kernel and its coefficient formulas.
The source phase is

    phi(x)*r^3 - phi(x+h)*(r-h)^3 + xi*(2*h*r-h^2).

A large entry needs simultaneous information on phi(x)-phi(x+h) at N^(-3)
and 3*h*phi(x+h) at N^(-2), with a common bounded positive multiplier.
The existing leading-coefficient Weyl theorem alone is insufficient.
F29 now proves that these two relations yield returns for the original
current-row phi(x), the actual large-entry count and scalar Schur bound,
uniformly in xi. UniformHorizontalConstantFreezing and complete affine
freezing follow from the explicitly unproved CubicTwoCoefficientWeylInput.
No separate degree-zero core estimate is assumed in these final theorems.
See CONSTANT_FREEZING_INTERFACE.md for the exact external input boundary.

The higher-degree and general structural interfaces also remain open.
WeightedCapture and P0 are not proved. The twelve deferred erroneous
three-dimensional applications remain unused, and U0 is unchanged.

## Checked files

- GMZP0/FourierTranslation.lean: exact Fourier algebra and counting-energy transfer.
- GMZP0/CyclicInput.lean: finite injection, zero extension, original endpoint recovery.
- GMZP0/ConstantFourier.lean: actual cubic-plus-quadratic fibers and the original estimate reduction.

The checkpoint adds 23 theorem declarations. Build and transitive-axiom
results are recorded in verification/result.json; theorem counts are an
audit inventory, not a percentage of the mathematical proof completed.
