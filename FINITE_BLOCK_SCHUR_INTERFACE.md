# Finite block Schur interface — F23

This checkpoint proves an elementary part of the manuscript's freezing
argument. It does not prove the structural large-block count, the full freezing
theorem, WeightedCapture or P0. No external deep theorem is used in these proofs.

## Exact operators and conventions

The input is `InputBox N = Fin (2*N) × Fin (2*N^2)` and the output is the
original `Base N = Fin N × Fin (N^2)`. The matrix `responseKernel N p` acts
as `finiteResponse N p`, with all original labels r=1,...,N and the exact
original parabola endpoints. For an original function f, restriction to the
input box gives exactly `response N f z (p z)` at every base point.

Write E(g)=sum |g|^2. `KernelEnergyBound B s` means

    for every complex vector g, E(Bg) <= s^2 E(g).

This is an actual finite operator estimate, not a placeholder proposition
standing for freezing. It is stated with finite sums and proved using the
linear-first pairing convention already used by the original adjoint formulas.

`FiniteSchur.lean` proves adjoint transfer in both directions, the scalar
row/column Schur bound, symmetric nonnegative quadratic-form domination, and
the square-root conversion from energy to norm. `BlockSchur.lean` regroups
the exact Gram energy into complete horizontal blocks before taking norms.
If symmetric nonnegative a(x,x') bounds those blocks and every row sum is at
most R, then

    E(Kg) <= R E(g),
    sqrt(E(Kg)) <= sqrt(R) sqrt(E(g)).

No positivity or regularity of the phase profile is required.

## Original block size and arbitrary pointwise masks

For x!=x', actual endpoint collision uniqueness gives each nonzero matrix
entry absolute value N^(-2). There are at most N entries in each row; conjugate
symmetry gives the corresponding column bound. The finite row/column Schur
estimate proves the complete original horizontal block bound 1/N. The
diagonal is the already checked I/N. These statements require N>0.

For any complex mask m with |m(z)|<=1, define K_m(z,u)=m(z)K(z,u). The exact
Gram block is

    B_m(x,x')(y,v) = m(x,y) B(x,x')(y,v) conjugate(m(x',v)).

Both multipliers are contractions. Their values may depend arbitrarily on
the original base point. The masked block still satisfies the 1/N bound.
The proofs do not replace a pointwise mask with a whole horizontal row.

## The count premise and what follows from it

For H a finite set of horizontal coordinates and v>=0, define

    L_x = {x' in H : x'!=x and the actual K_m Gram block
           fails KernelEnergyBound at v/N}.

The definition uses the compressed block itself. Its symmetry is proved
by the exact block-adjoint identity. A large uncompressed block need not stay
large after masking; no such inference is made.

Assume rho>=0, the mask vanishes off H, and for every x in H,

    |L_x| <= rho*N.

Then `kernel_energy_of_few_large_blocks` and its original-response wrapper give

    E(m * finiteResponse N p g) <= (rho+v+1/N) E(g).

The proof constructs an explicit symmetric coefficient matrix: zero outside H,
1/N on the diagonal and on large blocks, and v/N on the remaining blocks.
The three row contributions are bounded by 1/N, rho and v, respectively.
The 1/N diagonal term and the final square root are both retained.

For the same original one-bounded f, the input box has 4*N^3 elements, hence

    sum_z |m(z) response N f z (p z)|^2
      <= 4*N^3*(rho+v+1/N).

This keeps the complete original response. It does not by itself select a
positive original-weight subset or a finite frequency list.

## Connection to the existing minor-arc interface

`minorOutputMask Q N p` is exactly 0 at `MajorArc Q N (p z)` and 1 otherwise.
Taking H to be all horizontal coordinates gives

    the displayed large-compressed-block count
      => FiniteMinorEstimate Q N (sqrt(rho+v+1/N)) p.

The count is an explicit premise; its validity for the manuscript's structural
profiles is still to be proved. It is not added as an axiom.

`uniform_finiteMinorEstimate_of_compressed_counts` has the following order:

    for every s>0,
      there exist rho>0, v>0, N0>0,
      for every N>=N0, every Q and every p,
        if the actual compressed-block count holds,
        then FiniteMinorEstimate Q N s p.

The error-budget proof takes rho=v=s^2/4 and N0=B+1 for a natural B>2/s^2.
Thus all three parameters precede N,Q,p and, in particular, the original
f,theta,lambda,mu. This does not prove the existence of Q or establish a
uniform structural count.

## Exact obstruction checked first

For the one-dimensional matrix K=1/2, the Gram row sum is R=1/4 but
E(K*1)=1/4>R^2 E(1)=1/16. The Lean theorem
`gram_row_bound_needs_square_root` proves this with exact arithmetic.
It refutes replacing the operator bound sqrt(R) by R; it is not a P0
counterexample and is not a finite experiment offered as a general proof.

## Remaining core obligations

1. Prove the manuscript's phase-based large-block estimate (Section 2,
   eq:large-block) and its many-lag/root consequence. The present Schur bound
   does not establish that different estimate. Each successful k may have its
   own root y and interval; neither may be synchronized without proof.
2. Match the finite original blocks to the required whole-integer profiles,
   then justify compression and all boundary/support restrictions. An
   arbitrary masked subset of labels cannot simply be called an interval.
3. Derive forced relations for the actual structural observations, carry out
   the ordinary-polynomial and nilpotent descents, and prove the required
   uniform compressed-block counts on the no-relation part.
4. At F24, supported approximation error, exact child assignments and the
   conditional one-step assembly are checked; see FREEZING_STEP_INTERFACE.md.
   Actual branch-preserving structural constructions and uniform termination
   with constants before unrestricted real data remain open.
5. Complete structural value output types, external-input matching and
   realization from the F22 prepared cubes, then connect to finite capture.

External deep inputs remain explicit assumptions under the user's current
scope. Historical erroneous three-dimensional composite applications remain
unused; this checkpoint makes no claim about U0.
