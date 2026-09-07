# Direct proof of the twisted cube bound (checked at F19)

The route below has now been implemented in CubeDerivative.lean,
FiniteCrossCorrelation.lean and TwistedCube.lean, and passed the full F19
build and transitive axiom audit. LocalGlobalComparison.lean closes the
previously explicit twist premise. TwistObstructions.lean proves the exact
one-dimensional obstruction. The earlier planning filename is retained for
stable references. This is a proof of this comparison, not of P0.

Use the existing additive cube convention and set

    D_h H(Y) = H(Y) * conj(H(Y+h)).

The Boolean first-coordinate split gives, for all d>=0,

    T_(d+1)(H; psi_0,...,psi_d)
      = E_h psi_0(h) * T_d(D_h H; psi_1,...,psi_d).

Here T_s is `globalTwistedCubeMean s`. In dimension one,

    T_1(H;psi) = |H_hat(psi)|^2 >= 0.

For dimension two, taking a modulus and dropping the unit psi_0 factor yields

    |T_2(H;psi_0,psi_1)| <= E_h |(D_h H)_hat(psi_1)|^2.

The right side equals

    sum_phi |H_hat(phi)|^2 * |H_hat(phi+psi_1)|^2.

To verify the signs carefully, set

    C_(F,G)(h) = E_Y F(Y+h) * conj(G(Y)).

Then (D_h H)_hat(psi) is conj(C_(H,H*conj(psi))(h)). The normalized Fourier
transform of C_(F,G) is F_hat(phi)*conj(G_hat(phi)), while the transform of
H*conj(psi) at phi is H_hat(phi+psi). Parseval gives the displayed energy.

Put a(phi)=|H_hat(phi)|^2. The finite sum of a(phi)*a(phi+psi) is bounded by
sum_phi a(phi)^2: sum (a(phi)-a(phi+psi))^2 >=0, and character translation
is a finite bijection. At psi=0 the energy is exactly the untwisted global
second moment. Thus the desired bound holds in dimension two.

For dimensions s>=3, apply the first-coordinate recurrence, the finite
triangle inequality, and the already proved bound in dimension s-1 to each
D_h H. The resulting average of untwisted (s-1)-moments is exactly the
untwisted s-moment, by the same cube recurrence. This proves the specific
character-twist inequality for all s>=2 without requiring a general mixed
cube inequality as a prior theorem.

Dimension one must be excluded: a nontrivial character has zero untwisted
first moment but twisted first moment one at its own character. That exact obstruction is proved alongside the base case.

All the listed finite Fourier, derivative, recurrence and induction steps
are now checked. The family theorem still needs its separate formal proof.
