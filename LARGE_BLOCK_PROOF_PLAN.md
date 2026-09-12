# Next core target: the actual phase-based large-block estimate

Status at F25: the finite enlargement, exact original-block compression,
complete phase estimate and uniform many-lag/root consequence below are now
implemented and checked. See WIDE_BLOCK_INTERFACE.md for the exact statements
and scope. The remainder of this document records the original F24 proof plan.

## Boundary issue found by reading the actual code

`horizontalBlock_action_integer_labels` in IntegerBlockFormula.lean gives the
complete I_h formula under SafeVertical and bounded-gap hypotheses. The
corresponding double-label identities also keep these safe-source assumptions.
They cannot be applied as unrestricted original-box formulas in freezing.

For an arbitrary original vertical row, compressing both sides of the
whole-integer block can truncate the inner r sum in BB*. The absolute value
of such a truncated sum need not be bounded by the absolute value of the
complete sum. Triangle inequalities alone do not repair that comparison.

## Proposed finite enlargement

Use the actual x,x' in Fin N, with h=x'-x nonzero, and a supplied full-integer
frequency field P(x,y) agreeing with p(x,y) at every original base point.
For any r,s in {1,...,N} with r-s=h, the target coordinate is

    v = y + r^2 - s^2 = y + 2*h*r - h^2.

For 1<=y<=N^2 this target belongs to [1-N^2, 2*N^2]. A finite enlarged
vertical input type of size 3*N^2 therefore contains every original target
for every valid original label, without SafeVertical. Represent its integer
coordinate by index+1-N^2 and embed original y at index y-1+N^2.

Define the widened block with original vertical output rows and this enlarged
input, using the complete I_h sum and the same phase

    e(P(x,y)*r^3 - P(x',v)*(r-h)^3)/N^2.

The proposed proof must show:

1. All displayed target indices are in the enlarged finite input, and the
   original vertical embedding is injective and preserves input energy.
2. Widened-block action on the zero extension of an original input is exactly
   the original finite horizontal block. This equality must use the existing
   original endpoint/collision formulas and the supplied agreement of P,p.
3. An energy bound for the widened block consequently bounds the original
   block. No direct comparison of truncated and complete exponential sums is
   made. A further pointwise output compression is controlled by F23.
4. In the widened block's Gram kernel, every admissible common target is
   present, so the shared-target sum retains the complete original labels.
   Reindex the two labels as r+k,r, with exact overlap I_h intersect (I_h-k).
   Off-diagonal output displacement is exactly 2*h*k.
5. The k=0 term costs at most N/N^4, and the complete off-diagonal terms give
   the paper's double phase and the N^(-4) normalization. Bound the resulting
   row sums by the displayed sum of absolute complete exponential sums, then
   apply the proved finite Gram-row Schur theorem.
6. From failure of the v/N block bound, extract sufficiently many nonzero
   lags with sums of size c_v*N, once a threshold depending only on v holds.
   Keep actual successful roots and intervals. The paper permits different
   roots for different k; do not impose simultaneous choices without proof.

The field P in this step is supplied and total on the needed integer inputs.
The existing `originalFieldExtension` agrees with the original data but uses a
fallback outside the box. That fallback extension cannot automatically be
called an ordinary polynomial or a structural observation. Structural claims
must use the actual full profile formulas and their verified original-box
agreement.

## Subsequent obligations

After the finite phase estimate is checked, connect it to coefficient
extraction and actual structural relations. General-degree Weyl and the deep
structural inputs remain explicit external dependencies in the present scope.
All coefficient identities, denominator bookkeeping, root branches, rational
descents, child construction and uniform termination still require core
proofs. F24 already provides the final conditional assembly once their real
outputs and counts are supplied.

The completed F25 construction does not prove P0, WeightedCapture or uniform freezing. It does
not reactivate any deferred three-dimensional composite application.
