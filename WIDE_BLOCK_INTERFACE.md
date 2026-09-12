# Complete phases for original finite blocks: F25

The five F25 modules contain 42 new kernel-checked theorem declarations.
The full-project audit is recorded in verification/result.json. The target P0
and WeightedCapture are still unproved. These modules use no external deep input.

## Boundary correction and exact original operator

The manuscript's section 2, equations (block), (double-phase) and (large-block),
uses the full integer vertical line. The earlier finite complete-label formulas
required a safe source window. That restriction cannot simply be discarded
when applying freezing to all original points.

In general a truncated exponential sum is not bounded by the modulus of the
complete sum: the two unit terms 1 and -1 give an exact checked obstruction.
F25 therefore enlarges the finite vertical input, before forming its Gram
kernel. It does not make a truncated-versus-complete modulus comparison.

For every original y in [N^2] and valid original label r in I_h, the exact
target y+2hr-h^2 belongs to [1-N^2,2N^2]. The widened input has 3*N^2 points
and contains every such target, including those from boundary source rows.
The original vertical input embeds with its actual integer coordinates.
Zero extension preserves the input energy exactly.

A total field P : Fin N -> Z -> Frequency is supplied together with

    forall x,y in the original box, P(x,label y) = p(x,y).

The widened block on the zero extension of any original input is exactly the
original horizontal block, at every original output row. Its energy bounds
therefore bound the original block and any further pointwise complex mask
with modulus at most one. The comparison is for the same input; it does not
replace the original function or any original response.

An arbitrary agreeing extension is not asserted to be a polynomial observation.
Later structural applications must use their actual global formulas as P.

## Complete phase estimate

Write h=x'-x and use the manuscript's circle-valued double phase

    Q(y,h,k,r) = P(x,y)*(r+k)^3 - P(x,y+2hk)*r^3
                - P(x',y+2h(r+k)-h^2)*((r+k-h)^3-(r-h)^3).

Let L(y,k) be the sum of e(Q(y,h,k,r)) on the exact overlap
I_h intersect (I_h-k). The widened Gram entry at y,t is exactly

    N^(-4) * sum_{k in [-N,N]} 1_{t=y+2hk} * L(y,k).

This is an equality of complex sums before absolute values are introduced.
The pair reindexing theorems are generalized to an arbitrary additive
commutative monoid so they apply directly to complex phases. All multiplicities
and original labels remain. The zero-lag phase is zero and L(y,0)=|I_h|<=N.

If M(k)>=0 bounds |L(y,k)| for every original y and nonzero k, then every
widened input u satisfies

    E(B_wide u) <= (N + sum_{k != 0} M(k))/N^4 * E(u).

The finite Gram-row estimate supplies the square root when interpreted as an
operator norm bound. No square root is silently removed.

## Successful lags, exact order of quantifiers

For v>0 and N*v^2>=2, failure of the actual compressed original block bound
v/N gives a finite set K and original source roots y(k) such that

    |K| >= N*v^2/4,
    every k in K is nonzero and |k|<N,
    |L(y(k),k)| >= N*v^2/8.

The proof maximizes each complete lag sum over the finite original source
rows. Roots are allowed to depend on k. No common root, common successful
interval, or simultaneous connection is inferred.

The final exported uniform theorem has this order:

    forall v>0,
      exists c>0 and a positive N0,
        forall N>=N0,
          forall P,p agreeing on the original box,
          forall contractive masks m and original x!=x',
            failure of the actual masked original v/N block bound
            implies existence of K and y(k), with |K|>=c*N
            and the above nonzero-lag and complete-sum conclusions at c*N.

One can take c=v^2/8 and N0=B+1 for a natural B>2/v^2. The root choices and
successful set are after N and the original data, as required. The actual
compressed-block hypothesis is not a claimed consequence of a formal symbol.

Only the chosen source y(k) is asserted to be an original point. Other field
arguments in its complete phase sum can lie outside the original box; this is
why P is supplied on the full integer line. The theorem gives no original
response or retained connection at such outside points. Their values must
come from the genuine total structural profile in later applications.

## What remains

F26 now proves the D=1 specialization through the actual no-relation operator,
including both coefficient identities, returns in k and h and the compressed
block count. See AFFINE_FREEZING_INTERFACE.md. The general-degree obligations
below remain; their D=1 portion was the frontier immediately after F25.

This completes the phase estimate and many-lag interface needed for the
original finite operator. It does not formalize the full infinite-line
operator as a separate theorem, and that theorem is not needed by the present
finite original-box bridge.

The next ordinary-polynomial step must attach actual polynomial coefficients
to Q, record the appropriate one-variable Weyl input, retain its denominators,
and remove k and h using the required return estimates. In reverse-direction
arguments one must use the adjoint symmetry of the actual original compressed
Gram blocks. The rectangular widened blocks are not asserted to be mutual
adjoints. Apply the checked widening comparison separately in each direction.

For D>=2 the relevant leading coefficient is -3k(2h)^D*a_D(x+h), independent
of y. For D=1 both directions and the integer factor 8 must be retained.
These polynomial identifications and their arithmetic consequences are not
conclusions of F25's arbitrary-field phase theorem.

Structural compressed-block counts, rational model construction, all descent
steps, and uniform termination remain open. F24 supplies a conditional final
assembly after their actual outputs are available. External deep proofs remain
outside this phase; precise hypotheses must still be supplied and checked at
their uses. The twelve deferred three-dimensional applications remain unused.
