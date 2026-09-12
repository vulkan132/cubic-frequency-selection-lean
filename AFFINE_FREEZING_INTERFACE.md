# The affine no-relation operator: F26

F26 implements the actual degree-one block and row relations from the
ordinary-polynomial starting case of the manuscript. Its six modules contain
25 theorem declarations. These are core proofs; no external deep theorem is
used in this checkpoint. The full-project audit is recorded separately in
verification/result.json. P0 and WeightedCapture remain unproved.

## Actual profiles, phases and intervals

The full integer affine profile is

    P(x,y) = y * a(x) + b(x) in R/Z.

The slopes and intercepts are unrestricted, with arbitrary horizontal
dependence. The implementation also proves exact equality with the integer
evaluation of every real affine formula. Its original-box restriction agrees
at every original point, and it supplies the actual outside-box values used
in F25's widened phase. No arbitrary fallback extension is called a polynomial.

The exact double phase is a cubic circle polynomial in the original label r.
All four coefficients are explicit. Its cubic coefficient is

    -2*h*k * (a(x) + 3*a(x+h)).

It is independent of the successful root and both intercepts. The reverse
direction has coefficient 2*h*k*(3*a(x)+a(x+h)), with its own k and root.
Actual lag-label sets are proved to be the exact integer interval cut out by
the four original label constraints, including empty cases.

The existing proved cubic Weyl theorem is transferred to every such shorter
interval, still dividing its sum by the original N. One positive denominator
is fixed before N, interval endpoints and all cubic coefficients. This step
uses the actual interval length and costs the stated factor rho^(-3); it does
not silently renormalize by a shorter interval or invoke an external Weyl input.

## From a large block to a slope relation

The affine return theorem is now packaged for every positive error exponent m:
a positive density of returns at scale C/N^m gives a bounded positive multiple
of the slope at scale E/N^(m+1). Its constants precede m,N and the data. A second
version retains the actual dense fiber of bounded positive multipliers before
combining them. Neither theorem is a general monomial-in-h return result.

For each v>0, Q,E,N0 are chosen before N, the affine profile, arbitrary pointwise
contractive mask, and the original horizontal points. Failure of the actual
compressed v/N block bound then gives a bounded positive n with

    ||n*h*a(x)|| <= E/N^4.

The proof first obtains the two directional combinations. Reversal uses the
checked adjoint symmetry of the original compressed Gram blocks; it makes
no claim that the rectangular widened blocks are mutual adjoints. The two
successful lag/root families need not intersect.

Elimination retains exactly 8*n1*n2. An exact checked obstruction takes both
slopes to be 1/4 in R/Z: both directional combinations vanish, but the slope
has norm 1/4. Thus the integer multiplier cannot simply be cancelled.

## Actual row counts and the no-relation operator

For every v,rho>0 there are Q,E,N0, before all original data, such that a row
with at least rho*N actual large compressed blocks satisfies

    AffineTopRelation(Q,E,N,a(x)):
      exists integer 1<=q<=Q with ||q*a(x)|| <= E/N^5.

The proof reindexes actual neighboring horizontal points injectively by h,
preserves their count, and uses the bounded-multiplier return theorem again.
Its contrapositive gives strictly fewer than rho*N large blocks on every row
without the displayed relation. This count is proved, not supplied as a premise.

The final operator theorem has the following order of quantifiers:

    for every s>0,
      there exist positive Q,E,N0,
        for every N>=N0, every slope/intercept field a,b,
        and every pointwise mask m with |m|<=1,
          if m vanishes on rows with AffineTopRelation(Q,E,N,a(x)),
          then for every original input g,
            E(m * A_affine(g)) <= s^2 * E(g).

The canonical mask removes precisely those relation rows and retains any
given original pointwise mask elsewhere. An identically zero row has no large
Gram blocks. The proved counts therefore apply on every row, and F23's Schur
bound gives the displayed error after choosing rho,v,N0 before all data.
The input g, original output points, original labels and full response are
the same throughout. The norm bound is s, and the squared-energy bound is s^2.

Here Q bounds a slope multiplier; it is not a claimed final major-arc cutoff
for the value P(x,y). The theorem does not say relation rows have a small
operator norm or that their original frequencies are already captured.

## Remaining core interfaces

F27 now constructs the actual finite list of constant-in-y children on relation
rows, retaining every rational residue and circle root in the explicit grid.
The list size, offsets, actual point assignment and circle approximation have
the required prior quantifiers. Their connection to F24's freezing assembly
is checked, leaving precisely the degree-zero core premise for complete affine
freezing. See AFFINE_CHILD_INTERFACE.md.

F29 now proves the degree-zero starting case and complete degree-one minor-arc
theorem conditional on the explicit CubicTwoCoefficientWeylInput. The external
input is not a new axiom or a proved theorem; see CONSTANT_FREEZING_INTERFACE.md.
For D>=2, F30 proves the genuine polynomial coefficient identities and
single-block relation from an explicit Weyl premise. F31 constructs actual
ordinary children and connects degree induction conditional on the internal
MonomialDenseReturns lemma. F32 proves that lemma and completes ordinary
freezing from the two external Weyl inputs. The
generic structural model case, realization, rational descents and uniform
termination also remain open. See ORDINARY_DESCENT_INTERFACE.md.

External deep proofs remain outside the current work phase. The historical
twelve incorrect three-dimensional composite applications remain unused;
no new claim about U0 is made.
