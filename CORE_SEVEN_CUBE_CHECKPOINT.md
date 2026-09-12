# F21: core extraction through real seven-cubes

Date: 2026-09-12. This checkpoint follows the user's instruction to prioritize
the paper's core arguments and leave external deep theorems as explicit inputs.

## Checked core estimates

For positive labels h,h'<=N, integer radius s with 2s<N, N<=A*h' and
gcd(h,h')<=A, every integer value h*v+h'*v' has at most 1+2*A^2 representations
with |v|,|v'|<=s. The proof injects representations into integer codes using
Bezout divisibility; it does not assume a primitive-kernel parametrization.
For q>4N^2 the actual map 2h*v+2h'*v' modulo q has the same bound, since its
integer values lie in (-2N^2,2N^2). All parameter multiplicities are retained.

On the actual positive labels 1,...,N, the events A*h<N, A*h'<N and gcd(h,h')>A
have total probability at most 3/A. The gcd bound uses exact finite counts of
multiples, independent pair sampling and the finite bound
sum_(d=A+1)^N 1/d^2 <= 1/A. It covers empty tails as well. For A=ceil(12/u),
the exceptional fraction is at most u/4.

With s=floor(u*floor(a*N/64)), the checked uniform radius threshold and actual
local-four bound give 2s<N and s>=u*a*N/256. Thus the actual density relative
to uniform group measure has energy at most

    C = 2^24 * (1+2*A^2) / (u^2*a^2).

If the paired local seventh-norm average exceeds u, a good pair has norm
greater than u/2, so the global seventh moment is at least (u/2)^128/C^7.
Applying this on the previously checked beta/2 proportion of good (x,j) fibres
and then using the complete frequency mesh gives real-zero seven-cube mass
at least chi = (beta/2)*(u/2)^128/C^7.

## Exact external boundary

`CyclicConcatenationInput` is a proposition, not a theorem or axiom. For every
beta>0 it asks for a single 0<u<1/8 before N,q,ell and H. For every positive N
and ell, every nonzero modulus q and every |H|<=1, an average local fourth norm
at least beta/2 implies a paired local seventh-norm average greater than u.
Shrinking acts on the integer parameter radius; image-set deduplication is
not permitted. Its intended source is Tao--Ziegler, Theorem 1.23, specialized
to rank one and degree four. The source audit does not discharge this input.

`uniform_original_real_seven_of_concatenation` proves the core implication
from that input and original admissibility. It chooses M,c,d,E,chi,N0 before
N,q,f,theta,lambda,mu. The modulus range is 4N^2<q<=128N^2; the already checked
prime choice 64N^2<q<128N^2 supplies this. It retains:

- the original safe window and a positive original mass;
- the same original weighted response and every supported pointwise response;
- one real lift F on all cyclic points, on the grid M_lift^(-1)Z, with |F|<=3;
- the supported circle error to d*theta at scale 19E/N^3;
- positive original weighted real-zero seven-cube mass for that same F.

This result captures differences of the lift of d*theta. It does not yet give
nilpolynomial values or finite candidates for theta. All circle roots remain
necessary in the later passage back to the original frequency.

## Verification and remaining core work

The F21 inventory has 712 checked theorem declarations, including the explicit
conditional results. All transitive axiom checks admit only propext,
Classical.choice and Quot.sound. External inputs are not counted as proved.
P0 and WeightedCapture remain unproved; no P0 counterexample is asserted.

Next core interfaces: threshold/collision deletion and original-mass recovery
around an explicit approximate-polynomial input; large-block finite operator
estimates; realization, uniform freezing and termination of descents. External
deep proofs are outside the current work phase. The historical twelve invalid
three-dimensional composite applications remain unused.

F22 update: the threshold/collision deletion, horizontal selection, exact
q^8 count and original-mass transport from supplied subsets listed above are
now checked. Structural output types and existence remain open; see
STRUCTURAL_VALUE_INTERFACE.md. The F21 count above is historical.
