# Original operator stability and the conditional freezing step — F24

This checkpoint formalizes the elementary final assembly in the manuscript's
Section 4. It does not prove the structural descents or the full uniform
freezing theorem. No external deep theorem is used by these new proofs.

The Section 4 freezing statement and its final assembly paragraphs were read
directly. The statement restricts the target to 0<s<=1. Its approximate
replacement has circle error a0/(2*N^3), where a0=s/(12*pi). These exact
conditions, rather than a summary of the argument, determine the interfaces.

## Original operator and complete-label stability

All inputs are vectors on the original finite `InputBox N`. Every response
continues to use all labels 1,...,N and the same exact parabola endpoints.
For arbitrary original-box frequency fields p, the F23 block estimate gives

    E(finiteResponse N p g) <= E(g),       E(g) = sum_u |g(u)|^2.

The positive averaging operator on |g| is also a contraction. For two fields
p,q, a pointwise output mask m with |m(z)|<=1, and epsilon>=0, assume

    for every z with m(z)!=0 and every original label r,
      |e(p(z)*r^3)-e(q(z)*r^3)| <= epsilon.

Then `masked_response_difference_energy` proves

    E(m * (finiteResponse N p g - finiteResponse N q g))
      <= epsilon^2 E(g)

for every original input g. The proof bounds each difference by epsilon times
the positive average of that same |g|. The norm-input comparison does not
replace the original function in the response conclusion.

The scalar circle condition

    ||p(z)-q(z)||_T <= epsilon/(2*pi*N^3)

on nonzero masked points implies the bound for every original label, and
therefore the true operator estimate. No claim is made that an arbitrary
averaged-label condition can be substituted in this operator proof.

## Actual pointwise child assignment

For any finite family F_i and a single-valued pointwise assignment j(z),
the masks m_i(z)=m(z) when j(z)=i and zero otherwise give the exact identity

    E(m(z) F_(j(z))(z)) = sum_i E(m_i(z) F_i(z)).

Assignments may vary at every original base point. Each child may have its
own major-arc cutoff Q_i. If the mask is supported where the chosen child is
minor, supplied `FiniteMinorEstimate Q_i N t p_i` gives

    E(m * finiteResponse N (p_(j(z))(z)) g) <= J*t^2 E(g).

For J>0 and t=s/(3*sqrt(J)), this is exactly (s/3)^2 E(g).

The exact obstruction is checked first: two maps from a one-dimensional input
to two disjoint output coordinates each have norm one, but selecting both
coordinates gives output energy two from input energy one. Disjointness
does not remove the J loss in the general energy bound.

## Major-arc direction and scale

The major-arc definition is the original one:

    MajorArc Q N a iff some 1<=q<=Q satisfies ||q*a||_T<=Q/N^3.

For N>0, Q>=2*Q_i and ||a-b||_T<=1/N^3, every child's major-arc witness for b
also witnesses that the parent a is major. The usable contrapositive is

    parent minor and the stated circle closeness => chosen child minor.

No division on the circle is used, and no root branch is discarded.
An exact counterexample proves that closeness is needed: at N=4, b=0 is in
MajorArc 1 4, while a=1/4 is outside MajorArc 2 4.

The manuscript's error scale is matched by the checked identity

    (s/(12*pi))/(2*N^3) = (s/12)/(2*pi*N^3).

For 0<s<=1 this is at most 1/N^3. Thus the same supported error controls both
the response operator difference and the required major-arc transfer.

## Exact three-piece assembly

Let A be the actual set assigned to the no-relation part, with no regularity
assumption, and split the parent minor mask m into m_A and m_R on A and its
complement. For the supplied assigned child field q, the exact output identity is

    m A_p g = m_A A_p g + m_R (A_p g - A_q g) + m_R A_q g.

The finite energy triangle inequality is proved with constant one. Supplied
norm bounds s/3, s/12 and s/3 for these three pieces consequently imply the
parent energy bound s^2 E(g). The code proves the budget at the squared-energy
level and retains the correct square roots when combining the pieces.

`finiteMinorEstimate_freezing_step` applies this to the actual parent minor
mask, supplied approximating children and their individual minor estimates.
This is a conditional assembly result, not a proof that the children exist.

## Uniform numerical wrapper and exact outstanding premises

`uniform_freezing_step_from_compressed_counts` connects this assembly directly
to the F23 actual compressed-block count. Its quantifier order is

    for every 0<s<=1,
      there exist rho>0, v>0, N0>0,
      for every N>=N0, J>0, Q, child cutoffs Q_i,
      and every p, supplied children p_i, assignment j and actual set A,
        if the three conditions below hold,
        then FiniteMinorEstimate Q N s p.

The conditions are:

1. Q>=2*Q_i for each child, and on parent-minor points outside A the selected
   child has the displayed circle error (s/12)/(2*pi*N^3).
2. Every horizontal row has at most rho*N large Gram blocks for the actual
   parent operator compressed by its minor mask and the pointwise A mask.
   Large means failure of the complete vertical block bound v/N.
3. Each supplied child satisfies its own finite minor-arc estimate at
   tolerance s/(3*sqrt(J)).

The numerical rho,v,N0 are fixed before N,J,Q, all profiles and assignments.
The second condition proves the no-relation estimate using F23. The wrapper
does not assume a parent FiniteMinorEstimate as a premise.

The current proof does not produce the rational child types, any globally
defined structural observation formula, a uniform list of children, or the
parent cutoff Q. Nor does it establish the displayed block count for the
manuscript's structural profiles. The original scalar circle roots are covered
by earlier lemmas; incorporating every root branch into actual structural
descents remains an obligation.

F25 now completes the phase-based large-block estimate, many-lag/root
extraction and the finite boundary interface; see WIDE_BLOCK_INTERFACE.md.
F26 proves the actual compressed-block count and small operator bound for
the no-slope-relation part of affine vertical profiles, with constants before
all original data. F27 constructs their actual constant-in-y children and
checks complete affine freezing conditional only on the exact degree-zero
core case. F29 supplies that starting estimate from the explicit external
CubicTwoCoefficientWeylInput and thereby completes the internal affine proof.
The analytic input remains unproved. See CONSTANT_FREEZING_INTERFACE.md,
AFFINE_FREEZING_INTERFACE.md and AFFINE_CHILD_INTERFACE.md.
To complete the core argument, the remaining work includes actual structural
block counts, structural value realization, each rational descent and
uniform termination. A finite dependency tree and its uniform constants must
be established from those constructions, not inferred from this one-step
implication. WeightedCapture and P0 remain unproved.

External deep proofs remain outside the current work phase, with their exact
specializations recorded as explicit inputs. The twelve deferred erroneous
three-dimensional applications remain unused; no new claim about U0 is made.
