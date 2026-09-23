# Rational lower-central ideals of the original native Lie algebra — F63

Historical checkpoint. F64 extends the same witnesses with exponential-set
topology and exact original-lattice logarithmic spans; see
ORIGINAL_EXPONENTIAL_SUBSPACE_INTERFACE.md. Group integration remains open.

F63 adds 17 theorem declarations to F62's 1644. Full compilation and
axiom-audit records are in verification/result.json, build.log and
axioms.log. P0 and WeightedCapture remain unproved.

## Actual brackets and exact spans

For a fixed basis b of the actual real Lie algebra, bracketing the whole
algebra with an ideal N is proved to equal the real span of brackets
[b_i,v], where v runs through any actual spanning family of N. The proof
expands arbitrary original vectors in b and uses both bracket linearities.
It identifies the actual Mathlib Lie-ideal operation, not a substitute.

When C_ijk are the proved rational structure coefficients, bracketing b_i
with a vector of rational coordinates a has coordinates

```
(Phi_i(a))_k = sum_j a_j * C_ijk.
```

The coordinate formula is proved equal to the original Lie bracket.
Taking all i and all entries of a finite rational generator list therefore
gives the exact rational generator list for the next lower-central step.

## Recursive generators and the indexing convention

rationalLowerCentralGenerators starts with the rational unit vectors and
repeatedly applies Phi_i for every original basis index. The theorem
rational_lower_central_span proves that the real span of its original
vector images equals Mathlib's actual lowerCentralSeries at every depth.

Mathlib index 0 is the whole Lie algebra, index 1 is its commutator ideal.
The manuscript's group notation H_lc(1)=H uses a different index origin.
No identification of those indices, or of group and Lie-algebra series,
is made implicitly.

## Actual bases and common finite-depth bounds

A linearly independent subset of the finite original generator image is
selected and transported to the very same submodule using its proved
span equality. Every selected basis vector is an original generator,
so its original ambient rational coordinates are retained exactly.
This includes empty bases of zero-dimensional layers.

For each fixed finite depth r, one H>2 is chosen before every n<=r,
every selected layer-basis vector and every coordinate. H is obtained
from all the finite rational generator lists up to depth r. No unproved
uniform height bound on arbitrary rational presentations is used. This
is a collection of bases of the individual layers, not yet one common
ambient basis adapted to the entire flag.

## One original native Lie-algebra instance

The original smooth Lie-group structure supplies the real C^3 regularity
required by Mathlib's native Lie-ring instance. The regularity is derived
from the proved C-infinity structure; it is not a new premise.

original_weak_basis_lower_central_rational and
original_weak_basis_lower_central_bases apply the general proofs to the
actual GroupLieAlgebra in the original singleton chart. Their rational
tensor is the same one supplied by the original weak-basis record.

original_full_bounded_lie_filtration invokes the original structural
construction once and retains the original full integer/real basis,
entire original lattice, bounded native weak basis, smooth global
exponential/logarithm, literal arrays and their height/degree bounds.
The native lower-central ideals and their bounded bases are added within
that very same set of witnesses. The original real observations remain
unrestricted, and no extra project axiom or external theorem is introduced.

## Remaining group-filtration interface

This checkpoint establishes native Lie-algebra lower-central rationality.
It does not yet identify the original group lower-central subgroups with
the exponential images of those ideals, prove all required integrated
subgroup topology and original lattice-intersection properties, or obtain
the common adapted Malcev presentation and its quantitative metric data.
Those group-level matching obligations must be proved before invoking
the external adapted-basis or equidistribution conclusions.

General descent states and their coordinate changes still require
controlled rational families and quantitative termination. Final
original-frequency realization must preserve every original label,
circle root branch, quadratic freedom, weight and full response.
WeightedCapture/P0, P2-CSE and U0 remain open; the historical twelve
invalid three-dimensional composite applications remain deferred and unused.

New modules: LieBasisBracketSpan, RationalLieBracket, RationalSpanBasis,
RationalLowerCentral, OriginalRationalLowerCentral and OriginalFullLieFiltration.
