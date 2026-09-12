# Actual affine children and the degree-zero reduction: F27

F27 adds nine theorem declarations in CircleGrid, AffineChildren and
AffineFreezing. The actual finite children are constructed. Complete affine
freezing is reduced to the explicitly stated degree-zero core case; that case
is not proved here. No external deep theorem is used in these new proofs.
The full-project audit is recorded in verification/result.json.

## The finite list is explicit and retains all branches

The circle version of the existing major-arc grid now has the exact bound

    ||u - gridValue(N,epsilon,i)|| <= epsilon/(2*N^3).

It uses the same explicit gridIndices(Q,epsilon): each denominator q in [1,Q],
each residue j in {0,...,q-1}, and each integer l with
|l|<=ceil(Q/(q*epsilon))+1. Its value is j/q+l*epsilon/N^3 modulo one.
The proof keeps an actual circle root branch and rounds its actual small
remainder. It does not infer circle distance from the full-label metric.

On an affine relation row, ||q*a(x)||<=E/N^5 for an actual positive q<=Q.
For every original y in [N^2], the increment y*a(x) satisfies

    ||q*y*a(x)|| <= E/N^3.

Thus the increment lies in MajorArc(R,N) for R=max(Q,ceil(E)). The checked
grid supplies finite offsets and the actual children

    child_i(x,y) = b(x) + offset_i(N).

These profiles are constant in y, but retain arbitrary dependence on x.
The offset formula includes every allowed rational residue and remainder-grid
index. It is global on the original box, even when only some rows have the
slope relation. It is not a list of global constant-frequency candidates for
the original theta.

The exact quantifier order is

    for Q>0, E>=0 and epsilon>0,
      there exists a positive J,
        for every N>0 there are J offsets,
          for every slope field a there is an actual point assignment,
            for every intercept field b and every original relation point z,
              ||p(a,b,z)-child_assigned(z)(z)|| <= epsilon/(2*N^3).

J has no N or coefficient dependence. The offsets are before both a and b,
and even the assignment is before b. Parent-minus-child error is proved to
equal the original increment minus its offset exactly. No new original
function, response or point set is substituted.

## What the affine freezing theorem now assumes

UniformConstantFreezing is the following unproved core proposition:

    for every 0<s<=1,
      there exist positive Q,N0,
        for every N>=N0 and every b : Fin N -> Frequency,
          FiniteMinorEstimate(Q,N,s, z -> b(z.x)).

It is a function argument to the reduction theorem, not an axiom and not an
external deep theorem that has been declared established. This is precisely
the degree-zero starting case that remains to be proved.

Given this core proposition, uniform_affine_freezing_of_constant proves the
full finite minor-arc estimate for every unrestricted affine vertical profile.
The no-relation estimate, child construction, actual point assignment and
major-arc transfer are all supplied by existing checked results.

For a target 0<s<=1, the proof first selects the no-relation slope parameters
at tolerance s/3. Then it fixes the grid accuracy s/(12*pi) and obtains J.
The degree-zero input is invoked at s/(3*sqrt(J)), proved to lie in (0,1].
Only then are the final value major-arc cutoff 2*Qchild and maximum scale
threshold selected, before N,a,b. The circle error equals exactly the
F24 operator scale (s/12)/(2*pi*N^3). The same original input is used in the
three-piece energy estimate. There is no circular dependence of J on N or on
the subsequent child cutoff.

## Remaining work

F28 proves the degree-zero Fourier passage, including exact original-response
recovery and energy normalization. F29 proves the remaining internal horizontal
argument and complete affine freezing from CubicTwoCoefficientWeylInput.
The external analytic input remains unproved, so this is a conditional theorem,
not an unconditional project result. See CONSTANT_FREEZING_INTERFACE.md.
For higher polynomial
degrees, the coefficient identities, return estimates and actual degree descent
remain. The general structural value models, realization and structural
termination are also unfinished. P0 and WeightedCapture remain unproved.

All twelve deferred erroneous three-dimensional applications remain unused.
No new assertion about U0 is made. External deep proofs remain outside the
current work phase, and any future use must retain explicit exact hypotheses.
