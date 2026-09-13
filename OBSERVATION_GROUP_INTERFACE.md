# F33: exact observation group and original phase encoding

Update at F35: the exact commutator subgroup is now proved, and the F34
coordinate flag gives a uniform nilpotency bound for a nilpotent base.
Actual continuous characters have real-linear fiber parts annihilating W,
with original-source cancellation and lattice integrality. Full rational
and Lie/Malcev structures, bounded integer bases and boundary estimates
remain open. See OBSERVATION_NILPOTENT_INTERFACE.md for the current scope.

Update at F34: the abstract common-flag premise has been removed under
explicit actual triangular coordinate hypotheses. Weighted polynomial
lowering, uniform flag construction, proper W, and saturation of W cap V_Z
inside V_Z are now proved. The full rational Malcev presentation, rationality
and full lattice/basis obligations remain. See COORDINATE_FLAG_INTERFACE.md.
The F33 algebraic conclusions recorded below retain their exact scope.

P0 and WeightedCapture are still unproved. This checkpoint implements part
of the general structural freezing argument after the ordinary case.
It uses no new external analytic input and postulates no new axiom.

The source for this work is the actual manuscript
`../GMZ_P0_Arxiv_Paper/sections/04-freezing.tex`, especially the polynomial
module, semidirect product, fixed observation, and large-block curve sections.
The red-team report's Sections 9 and 10 identify the same algebraic interface.
The original Phase 12 and Phase 30 contracts were reread before this work.
Their original-response and circle-root restrictions remain in force.

## Constructed objects and checked identities

`ObservationModule G` is an actual real submodule of real functions on G,
closed under every pullback `T_g P(u) = P(g*u)`. In particular,
`T_h (T_g P) = T_(g*h) P`; the order is important for noncommutative G.
The module is not defined by assuming any later freezing conclusion.

`observationDifferenceSpace V` is the real span of the actual `T_g P - P`.
It is translation-invariant. A real linear functional annihilates this
space precisely when its value is invariant under all translations.
Every translation-invariant observation function is constant by transitivity.

`ObservationGroup V` is the actual group of pairs, with

    (g,P)*(h,Q) = (g*h, T_h P + Q),
    (g,P)^(-1) = (g^(-1), -T_(g^(-1)) P).

All group axioms are proved. For any actual subgroup Gamma of G, integer-valued
members of V form an additive subgroup, preserved by Gamma translations and
their inverses. The product Gamma times this subgroup is proved to be a
subgroup of the observation group. Its name `observationLatticeSubgroup`
does not assert discreteness, cocompactness or a full lattice property.

`ObservationSection Gamma` records an actual coset representative map c,
with c(g*gamma)=c(g) and g^(-1)*c(g) in Gamma. It does not yet assert boundedness
or piecewise smoothness. The correction is the actual element
gamma_g=g^(-1)*c(g), and gamma_(g*gamma0)=gamma0^(-1)*gamma_g is proved.
Right multiplication by (gamma0,Q0) changes P(gamma_g) by exactly the integer
Q0(gamma0^(-1)*gamma_g). Thus e(P(gamma_g)) defines a unit-modulus function
on the actual coset quotient, without requiring Gamma_H to be normal.

The curve point `(g, source*1 - A*T_g F)` evaluates to
`source - A*F(c(g))` exactly, in the reals and on the circle. Applied to the
full block phase, this gives `observation_block_circle_phase` and
`observation_wide_lag_sum` on precisely the original lag-label intersection.
The same root y, horizontal pair, target value, signs and multiplicities
are retained. Swapping the horizontal pair gives the reverse block without
equating the successful roots from distinct lag sums.

The associated finite response uses the same f and all original response
labels. These are identities for a supplied observation profile; they do
not prove that an arbitrary original theta has such a model.

An actual base character and a linear fiber functional annihilating W give
a group character on H. If 1 belongs to W, the source term vanishes and the
curve's character value is eta(g)-A*ell(F). The proof of 1 in W from an
explicit common lowering flag is also checked: choose the least flag level
containing a nonzero element of W; its differences vanish by minimality,
so it is a nonzero constant and can be rescaled to 1.

## Exact obstruction

`observation_missing_pullback_obstruction` uses a genuine affine real
observation module and the identity coset quotient. For g=1/2 and F(t)=t,
source=0 and A=1, the correct phase is -1/2 while the curve omitting T_g
has phase 0. Their circle distance is exactly 1/2. This is a counterexample
to the proposed algebraic omission, not to P0. The identity quotient is
used only to expose this algebraic identity; no cocompactness is claimed.

## Remaining structural obligations

1. Match the full rational Malcev polynomial module to F34's explicit
   triangular coordinate hypotheses. F34 now constructs the flag and proves
   W proper and its integer intersection saturated. Rationality of W and
   the full lattice and bounded-basis properties still need proof.
2. F35 proves nilpotence under the coordinate hypotheses and the full
   commutator structure of H. Prove bounded rational
   presentations and filtrations, and the polynomial degree of the actual
   observation curves. These are core obligations, not newly exempted
   external deep theorems.
3. Construct the bounded canonical sections, prove the fiber mean-zero
   and uniform boundary/Lipschitz estimates, and classify bounded integer
   horizontal characters. F35 supplies the actual continuous linear form;
   the bounded integer bases and their quantitative bounds remain open.
4. Apply the precisely stated external equidistribution input, derive the
   two actual relation types, construct every rational descent and all
   branch lists, and prove their uniform termination and error budgets.
5. Connect actual structural extraction/realization to the original theta
   on positive original weight, then finish capture and the P0 implication.

The already proved ordinary freezing theorem keeps its two explicit external
Weyl inputs. General structural freezing has not been proved by this algebra.
The twelve historical incorrect three-dimensional applications remain unused;
P2-CSE and U0 remain open. No hash or finite numerical check is used as a
replacement for a general mathematical proof.

## Verification

Run `python verify.py`. It builds the project and audits every explicit
project theorem for transitive axioms. F33 adds 35 theorem declarations;
the expected total is 1033. Group structures and quotient maps are checked
definitions, with their proof fields used by the audited theorems.
