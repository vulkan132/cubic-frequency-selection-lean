# Core interface around structural value extraction

Update at F36: the ordinary freezing chain is now checked from its two
external Weyl inputs, and the general observation group's algebra, coset
invariance and exact original-block phase encoding are implemented. Actual
triangular coordinate formulas construct the lowering flag and yield
nilpotence for a nilpotent base; the commutator subgroup and continuous
character decomposition are proved. The same bounded polynomial presentation
now gives finite dimension, and continuous coordinates give the actual
topological group. A rational translation matrix with surjective coordinates
gives a finite rational-coordinate span for W. This
does not supply the nilpolynomial output types, quantitative rational
structures or their realization. See OBSERVATION_RATIONAL_INTERFACE.md for
the current structural frontier. The F22 count/transport scope below is
unchanged, and P0 remains open.

Checkpoint F22 (2026-09-12): 740 audited theorem declarations, of which 28
are new in this checkpoint. Only standard Lean/Mathlib foundations occur.
The new results are in GlobalCubeCollision, GlobalCubeThreshold,
PreparedSevenFibers, OriginalFiberRetention and UniformPreparedSeven.

The user requested prioritizing the paper's own core arguments and leaving
external deep proofs outside this work phase. The paper's Section 3 and the
real approximate-polynomial specialization in Section 2 were read directly
on 2026-09-12 for this interface.

## Preparation, with the exact original data

Start with the F21 original weighted real seven-cube mass at least chi>0,
conditional on the explicit uniform concatenation input. Put tau=chi/512.
The same F and the same cyclic extension of sigma=N^3*mu*1_D are used throughout.

The global cube is parameterized by (Y,v_1,...,v_7) in (ZMod q)^8, with all
128 Boolean vertices. The weighted loss from a cube with any vertex below
tau is at most tau: its nonnegative product is at most that factor. This
improves on, and in particular implies, the paper's conservative 128*tau bound.

For any two different Boolean vertices, changing one separating coordinate
gives at most one collision value. This works in every finite abelian group;
prime-field division is unnecessary. There are 8128 unordered vertex pairs,
so deleting all collisions costs at most 8128/q. A threshold chosen from chi
before N and the original data makes this loss at most chi/4.

The prepared distinct, thresholded, real-zero seven-cubes therefore have
horizontal average density at least chi/2. A set H of at least chi*N/4
horizontal coordinates has density at least chi/4 on each fibre. The exact
count identity uses denominator q^8. Thus every x in H has at least
(chi/4)*q^8 such cubes with every vertex in {Y: sigma_x(Y)>=tau}.

`uniform_original_prepared_seven_of_concatenation` records this preparation
with constants M,c,d,E,chi,N0 chosen before N,q,f,theta,lambda,mu. It retains
the original safe window, original mass, full responses, grid and boundedness
of one F, and its supported circle error to d*theta.

## Transport after a structural subset has been supplied

Let S_x be supplied subsets of the threshold sets for x in H. If each S_x has
at least cModel*q elements, the positive threshold forces every selected
cyclic point to lie in the actual original vertical box and in D. Exact
preimage counting and the unchanged original weights give

    mu(A) >= |H|*cModel*q*tau/N^3.

If |H|>=rho*N and q>=64*N^2, this is at least 64*rho*cModel*tau. In the paper
rho=chi/4, giving 16*chi*cModel*tau. A supplied equality F_x=G_x on S_x
transfers the supported circle error to d*theta-G_x on A. The full original
response remains valid at every retained original point. No division by d
or deletion of circle root branches is performed.

These are transport statements. G is an arbitrary supplied function here;
the results do not label it a nilpolynomial or assert its existence.

## External and remaining core boundaries

The intended real approximate-polynomial input (Manners, degree six) must
provide a subset S_x and a real nilpolynomial G_x, with a uniform positive
cModel, complexity bounds and a prime threshold chosen from chi. Its proof
is outside the current work phase. The precise filtered nilmanifold,
bounded-lift and real-polynomial output types have not yet been implemented.
The count and transport steps above do not discharge that structural input.

Next core work includes encoding these structural output types and matching
their uniform hypotheses, finite realization, large-block operator estimates,
and uniform freezing with its descents and termination. P0 and WeightedCapture
remain open, and the historical twelve erroneous three-dimensional applications
remain unused.
