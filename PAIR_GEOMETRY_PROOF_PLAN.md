# Pair geometry after the family step (plan, completed at F21)

The F17 theorem records a>0 but does not record a<=1. Do not silently add that
upper bound. A weaker bound obtainable from the actual local-moment lower
bound suffices for the representation/no-wrap argument.

For an admissible input, all local norms are at most one and the full sampling
space is nonempty. Hence beta=(a/4)^16/(4*57^16)<=1. Since
4*57^16 < 64^16, this implies a<=256. This is a consequence under the actual
input hypotheses; it need not be added to the earlier uniform existential
statement in a vacuous input range.

For 0<u<1/8, ell=floor(a*N/64), and s0=floor(u*ell), this yields s0<N/2.
Therefore 2*h*v+2*h'*v' has absolute value <2*N^2 whenever h,h' are positive
labels at most N and |v|,|v'|<=s0. The difference of two such values has
absolute value <4*N^2<q for an actual prime q>64*N^2. That gives injectivity
of reduction on these integer values. This uses a slightly larger interval
than the manuscript's displayed (-N^2,N^2), with the already available stronger
prime lower bound. The final no-wrap conclusion is unchanged.

If h,h'>=N/A and gcd(h,h')<=A, the integer representation kernel is generated
by (h'/g,-h/g). Combining interval diameter 2*s0<N with h'/g>=N/A^2 gives a
representation count at most 1+2*A^2 (a sharper bound may also follow). Prove
the count with integer floors/cardinalities rather than treating these real
ratios as exact integers.

A threshold depending only on u,a gives ell>=a*N/128 and
s0>=u*a*N/256. Together with q<=128*N^2, the normalized parameter-density
energy is bounded by 2^24*(1+2*A^2)/(u^2*a^2). The generic density energy
formula is in ParameterEnergy.lean; the representation count is still open.

After a good pair with local seventh norm >u/2, work directly with moments:

    global seventh moment >= (u/2)^128 / C^7.

A proportion >=beta/2 of good (x,j) fibres then gives an average moment at
least beta*(u/2)^128/(2*C^7). This keeps all constants positive and fixed before
N and avoids needing a separate real fractional-power manipulation merely
to obtain the seven-cube lower bound. It must still be connected to the actual
family theorem, original field, fixed lift and complete mesh orthogonality.

F20 update: the elementary radius, bounded-value and no-wrap lemmas, bounded
event selection, uniform threshold, and the derivation a<=256 from the actual
local-four bound are audited in `PairGeometry.lean` and `PairScale.lean`.
The gcd representation count, exceptional-pair count and family theorem remain
open. `proof_drafts/F20Representations.lean` is an unfinished draft and is not
included in the audited checkpoint.

F21 update (2026-09-12): the gcd representation argument is now checked in
`GMZP0/PairRepresentations.lean`, including its cyclic consequence. The
unfinished F20 draft was promoted into that module. `ExceptionalPairs.lean`
proves the actual exceptional probability <=3/A<=u/4 by finite counting and
telescoping. `PairDensity.lean` and `PairSeventhMoment.lean` check the full
density and moment passage. `UniformOriginalRealSeven.lean` connects it to
the original data, conditional on `CyclicConcatenationInput`. The external
deep proof is outside the current work phase at the user's request; the core
pair geometry is complete. See CORE_SEVEN_CUBE_CHECKPOINT.md.
